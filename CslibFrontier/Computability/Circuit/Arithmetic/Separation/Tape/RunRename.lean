/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunWord

/-!
# Renaming the inputs of an automaton, and change of rings

An equivalence `φ : J ≃ J'` of the input names renames the channels (`Tape.Ch.congr`) and the
letters (`Tape.Letter.congr`). Renaming keeps what a run emits (`Tape.emit_congr`), so the value of
an automaton does not change when its letters and its inputs are renamed together
(`Tape.runVal_congr`). A ring homomorphism applied to the matrices maps the value
(`Tape.runVal_map`).

## Main definitions

* `Tape.Ch.congr`, `Tape.Letter.congr`.

## Main results

* `Tape.emit_congr`, `Tape.runVal_congr`, `Tape.runVal_map`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Nc.RunOne` and `Nc.End.Run`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

variable {S J J' Γ : Type}

/-- Renaming the input channels along `φ`. -/
@[expose] def Ch.congr (S : Type) (φ : J ≃ J') : Ch S J ≃ Ch S J' where
  toFun
    | .tp s b => .tp s b
    | .inp j => .inp (φ j)
  invFun
    | .tp s b => .tp s b
    | .inp j => .inp (φ.symm j)
  left_inv z := by cases z <;> simp
  right_inv z := by cases z <;> simp

@[simp] theorem Ch.congr_tp (φ : J ≃ J') (s : S) (b : Bool) :
    Ch.congr S φ (.tp s b) = .tp s b := rfl

@[simp] theorem Ch.congr_inp (φ : J ≃ J') (j : J) : Ch.congr S φ (.inp j) = .inp (φ j) := rfl

/-- Renaming the input channels in letters. -/
@[expose] def Letter.congr (S Γ : Type) (φ : J ≃ J') : Letter S J Γ ≃ Letter S J' Γ :=
  Equiv.optionCongr (Equiv.prodCongr (Ch.congr S φ) (Equiv.refl Γ))

variable [DecidableEq S] [DecidableEq J] [DecidableEq J']

/-- Renaming keeps what a run emits on each channel. -/
theorem emit_congr (φ : J ≃ J') (o : List (Letter S J Γ)) (z : Ch S J) :
    emit (o.map (Letter.congr S Γ φ)) (Ch.congr S φ z) = emit o z := by
  induction o with
  | nil => rfl
  | cons a o ih =>
    rw [List.map_cons, ← List.singleton_append, emit_appendR, ih,
      ← List.singleton_append (l := o), emit_appendR]
    congr 1
    rcases a with _ | ⟨z', γ⟩
    · rfl
    · have : Letter.congr S Γ φ (some (z', γ)) = some (Ch.congr S φ z', γ) := rfl
      rw [this, emit_some, emit_some]
      simp

variable {F : Type*} [CommRing F] {Q : Type} [Fintype Q] [DecidableEq Q] [Fintype Γ]
  [DecidableEq Γ] [Fintype S] [Fintype J] [Fintype J']

/-- **Renaming the inputs does not change the value** of an automaton. -/
theorem runVal_congr (φ : J ≃ J') (mu : Letter S J' Γ → Matrix Q Q F) (i e : Q) (t : ℕ)
    (u : J' → List Γ) :
    runVal (fun a => mu (Letter.congr S Γ φ a)) i e t (fun j => u (φ j)) = runVal mu i e t u := by
  unfold runVal
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (Letter.congr S Γ φ)) _ _ fun o => ?_
  have hl : List.ofFn (Equiv.arrowCongr (Equiv.refl (Fin t)) (Letter.congr S Γ φ) o) =
      (List.ofFn o).map (Letter.congr S Γ φ) := by
    rw [List.map_ofFn]
    rfl
  have hm : Matched (List.ofFn o) (fun j => u (φ j)) ↔
      Matched ((List.ofFn o).map (Letter.congr S Γ φ)) u := by
    unfold Matched
    refine and_congr (forall_congr' fun s => ?_) ⟨fun h j => ?_, fun h j => ?_⟩
    · rw [← emit_congr φ (List.ofFn o) (.tp s false), ← emit_congr φ (List.ofFn o) (.tp s true)]
      rfl
    · have h1 := emit_congr φ (List.ofFn o) (.inp (φ.symm j))
      rw [Ch.congr_inp, Equiv.apply_symm_apply] at h1
      rw [h1, h (φ.symm j)]
      exact congrArg u (φ.apply_symm_apply j)
    · exact (emit_congr φ (List.ofFn o) (.inp j)).symm.trans (h (φ j))
  rw [hl]
  by_cases h : Matched (List.ofFn o) (fun j => u (φ j))
  · rw [ite_eq_left h, ite_eq_left (hm.1 h), List.map_map]
    rfl
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hm.2 h')]

/-- **Change of rings**: the value of an automaton with the matrices mapped by a ring
homomorphism is the image of its value. -/
theorem runVal_map {K : Type*} [CommRing K] (f : F →+* K) (mu : Letter S J Γ → Matrix Q Q F)
    (i e : Q) (t : ℕ) (u : J → List Γ) :
    runVal (fun a => (mu a).map f) i e t u = f (runVal mu i e t u) := by
  unfold runVal
  rw [map_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [apply_ite f, map_zero, ← Matrix.map_apply (f := f), ← RingHom.mapMatrix_apply, map_list_prod,
    List.map_map]
  rfl

end Cslib.Circuits.Arithmetic.Separation.Tape
