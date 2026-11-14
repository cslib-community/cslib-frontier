/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Zero
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection

/-!
# The exact normalization cap

Project old port 2, then identify the now adjacent old ports 1 and 3. The composition is
literally `capPort`, including its free order `0,1,4,…` and the fresh auxiliary before all
old auxiliaries. No new genus argument or target-boundary premise is used.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString

/-- The projection-then-adjacent-fold label map is exactly the normalization cap map,
on free labels and on the entire old auxiliary block. -/
theorem capPort_project_zero (n a : ℕ) (x : Fin (n + 4) ⊕ Fin a) :
    Sum.map (zeroPort (1 : Fin (n + 3))) id
      (PPGadget.substitutePort a (PPGadget.hidePort (2 : Fin (n + 4))) x) =
        PPGadget.substitutePort a capPort x := by
  cases x with
  | inr x => rfl
  | inl x =>
    have htwo : (2 : Fin (n + 4)).val = 2 := Fin.val_two
    have hone : (1 : Fin (n + 3)).val = 1 := Fin.val_one (n + 1)
    have hone' : (1 : Fin (n + 2)).val = 1 := Fin.val_one n
    rcases Fin.eq_self_or_eq_succAbove (2 : Fin (n + 4)) x with rfl | ⟨j, rfl⟩
    · simp [PPGadget.substitutePort, PPGadget.hidePort]
    · rcases j with ⟨j, hj⟩
      simp only [PPGadget.substitutePort, PPGadget.hidePort, Fin.insertNth_apply_succAbove,
        Sum.elim_inl, Sum.map_inl]
      unfold capPort zeroPort Fin.succAbove
      simp only [Fin.lt_def, Fin.val_castSucc, htwo, hone, id_eq]
      split_ifs
      all_goals
        simp only [Sum.map_inl, Sum.map_inr, id_eq]
        have hjcast : (⟨j, hj⟩ : Fin (n + 3)).castSucc.val = j := Fin.val_castSucc _
        have hjsucc : (⟨j, hj⟩ : Fin (n + 3)).succ.val = j + 1 := Fin.val_succ _
        first
        | rfl
        | omega
        | congr 1
          apply Fin.ext
          change j - 1 = 1
          omega

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- The existing guarded cap interpreter has an ordered numerical witness from every
source witness. Old port 2 is hidden at auxiliary zero, old ports 1 and 3 coincide, and all
other free and auxiliary labels retain exactly their specified layout. -/
noncomputable def GadgetWitness.normalizationCap {n : ℕ} (_large : 2 ≤ n)
    {R : Set (Fin (n + 4) → Bool)} {g : PPGadget arity sem R}
    (w : GadgetWitness g) : GadgetWitness (g.substitute capPort) := by
  let h := (w.project (2 : Fin (n + 4))).normalizationZero (1 : Fin (n + 3))
  have hb : ((g.project (2 : Fin (n + 4))).relabelFree
      (zeroPort (1 : Fin (n + 3)))).body = (g.substitute capPort).body := by
    change (g.body.relabel (PPGadget.substitutePort g.numAux
      (PPGadget.hidePort (2 : Fin (n + 4))))).relabel
        (Sum.map (zeroPort (1 : Fin (n + 3))) id) =
          g.body.relabel (PPGadget.substitutePort g.numAux capPort)
    simp only [CSP.relabel, List.map_map]
    apply List.map_congr_left
    rintro ⟨r, scope⟩ _
    simp only [Function.comp_apply, Constraint.relabel, List.map_map, Function.comp_def,
      capPort_project_zero]
  exact ⟨h.certificate, by rw [← hb]; exact h.accepted⟩

end Cslib.Complexity.CSP.OrderedBoundary
