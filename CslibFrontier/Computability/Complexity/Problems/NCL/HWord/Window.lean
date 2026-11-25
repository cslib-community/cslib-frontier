/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Basic

/-!
# Reconfiguration inside a fixed interval

An H-word reconfiguration that fixes the endpoints of an interval extends to any larger
H-word containing that interval. The surrounding word stays unchanged.

## Main definitions

* `HWord.Window`: an interval of fixed length inside a word.
* `HWord.Window.patch`: replace that interval.
* `HWord.Window.FramedStep`: an H-word move fixing two prescribed endpoint symbols.

## Main results

* `HWord.Window.reachable_patch`: paste an endpoint-preserving fragment trajectory into a legal
  ambient word.
-/

public section

namespace Cslib.Complexity.NCL.HWord

/-- A contiguous interval of length `m` inside a word of length `n`. -/
structure Window (n m : ℕ) where
  /-- Index of the first position. -/
  offset : ℕ
  /-- The whole interval fits inside the ambient word. -/
  fits : offset + m ≤ n

namespace Window

variable {n m q : ℕ} (window : Window n m)

/-- The ambient index of a position inside the interval. -/
@[expose] def get (i : Fin m) : Fin n := ⟨window.offset + i.val, by have := window.fits; omega⟩

/-- Replace exactly the positions of the interval. -/
@[expose] def patch {α : Type*} (base : Fin n → α) (fragment : Fin m → α) (i : Fin n) : α :=
  if hi : window.offset ≤ i.val ∧ i.val < window.offset + m then
    fragment ⟨i.val - window.offset, by omega⟩ else base i

/-- Patching reads the supplied fragment at every interval position. -/
theorem patch_get {α : Type*} (base : Fin n → α) (fragment : Fin m → α) (i : Fin m) :
    window.patch base fragment (window.get i) = fragment i := by
  rw [patch, dite_eq_left (by dsimp only [get]; constructor <;> omega)]
  exact congrArg fragment (Fin.ext (by simp only [get, Nat.add_sub_cancel_left]))

/-- Replacing an interval by its existing contents preserves the whole word. -/
theorem patch_eq {α : Type*} {base : Fin n → α} {fragment : Fin m → α}
    (he : ∀ i, fragment i = base (window.get i)) : window.patch base fragment = base := by
  funext i
  rw [patch]
  split
  next hi => exact (he _).trans (congrArg base (Fin.ext (by dsimp only [get]; omega)))
  next => rfl

private theorem patch_legal {H : Digraph (Fin q)} {base : Fin n → Fin q}
    {fragment : Fin m → Fin q} (hm : 0 < m) (hb : Legal H base) (hl : Legal H fragment)
    (hfirst : fragment ⟨0, hm⟩ = base (window.get ⟨0, hm⟩))
    (hlast : fragment ⟨m - 1, by omega⟩ = base (window.get ⟨m - 1, by omega⟩)) :
    Legal H (window.patch base fragment) := by
  intro i j hij
  rw [patch, patch]
  split <;> split
  · exact hl _ _ (by dsimp only; omega)
  · have he : (⟨i.val - window.offset, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    have hi' : window.get ⟨m - 1, by omega⟩ = i := by
      exact Fin.ext (by dsimp only [get]; omega)
    rw [he, hlast, hi']
    exact hb i j hij
  · have he : (⟨j.val - window.offset, by omega⟩ : Fin m) = ⟨0, hm⟩ :=
      Fin.ext (by dsimp only; omega)
    have hj' : window.get ⟨0, hm⟩ = j := by
      exact Fin.ext (by dsimp only [get]; omega)
    rw [he, hfirst, hj']
    exact hb i j hij
  · exact hb i j hij

/-- A fragment legal move whose two endpoints retain their prescribed symbols. -/
@[expose] def FramedStep (H : Digraph (Fin q)) (hm : 0 < m) (first last : Fin q)
    (s t : Fin m → Fin q) : Prop :=
  Step H s t ∧ s ⟨0, hm⟩ = first ∧ t ⟨0, hm⟩ = first ∧
    s ⟨m - 1, by omega⟩ = last ∧ t ⟨m - 1, by omega⟩ = last

/-- An endpoint-preserving interval trajectory extends to the fixed ambient word. -/
theorem reachable_patch {H : Digraph (Fin q)} {base : Fin n → Fin q}
    {s t : Fin m → Fin q} (hm : 0 < m) (hb : Legal H base)
    (hr : Relation.ReflTransGen
      (FramedStep H hm (base (window.get ⟨0, hm⟩))
        (base (window.get ⟨m - 1, by omega⟩))) s t) :
    Reachable H (window.patch base s) (window.patch base t) := by
  refine Relation.ReflTransGen.lift' (window.patch base) (fun u v h => ?_) _ _ hr
  obtain ⟨i, _, he⟩ := h.1.2.2
  refine reachable_of_eq_off (window.patch_legal hm hb h.1.1 h.2.1 h.2.2.2.1)
    (window.patch_legal hm hb h.1.2.1 h.2.2.1 h.2.2.2.2) (window.get i) fun j hj => ?_
  rw [patch, patch]
  split
  next hin =>
    exact he _ fun hij => hj <| Fin.ext <| by
      have := congrArg Fin.val hij
      dsimp only [get] at this ⊢
      omega
  next => rfl

end Window
end Cslib.Complexity.NCL.HWord
