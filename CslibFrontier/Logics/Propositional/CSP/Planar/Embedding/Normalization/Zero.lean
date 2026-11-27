/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Rotation
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentifyAt
public import CslibFrontier.Foundations.Data.BitString.CyclicDifference.BoundaryKernel
import CslibFrontier.Foundations.Data.List.OfFnPositions
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Exact adjacent reductions in normalization

The actual `zeroPort` quotient identifies the chosen cyclic edge and preserves the precise
canonical survivor word. The last edge identifies the last port with port zero. Only the
boundary is distinct: repeated body occurrences, cutvertices and unused ports are allowed.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString

private theorem zeroLabel_kernel (n a : ℕ) (i : Fin (n + 2))
    (x y : Fin (n + 2) ⊕ Fin a) :
    Sum.map (zeroPort i) id x = Sum.map (zeroPort i) id y ↔
      Function.update id (Sum.inl (finRotate (n + 2) i)) (Sum.inl i) x =
        Function.update id (Sum.inl (finRotate (n + 2) i)) (Sum.inl i) y := by
  rw [Function.update_id_apply_eq_iff]
  cases x with
  | inl x =>
    cases y with
    | inl y => simpa only [Sum.map_inl, Sum.inl.injEq,
        Function.update_id_apply_eq_iff] using zeroPort_kernel i x y
    | inr y => simp
  | inr x => cases y <;> simp

/-- Deleting the chosen edge's first marker and applying its exact quotient yields all
canonical surviving free labels, including at the wrap edge. -/
theorem zeroPort_survivors (n a : ℕ) (i : Fin (n + 2)) :
    ((List.ofFn (Sum.inl : Fin (n + 2) → Fin (n + 2) ⊕ Fin a)).eraseIdx i.val).map
      (Sum.map (zeroPort i) id) = List.ofFn Sum.inl := by
  rw [List.eraseIdx_ofFn, List.map_ofFn]
  congr 1
  funext j
  exact congrArg Sum.inl (zeroPort_differencePort i j)

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- Every source gadget witness supplies the full ordered numerical witness for exactly
`relabelFree (zeroPort i)`, at arbitrary ordinary or wrap adjacency. No target provider or
restriction on the actual body is required. -/
noncomputable def GadgetWitness.normalizationZero {n : ℕ}
    {R : Set (Fin (n + 2) → Bool)} {g : PPGadget arity sem R}
    (w : GadgetWitness g) (i : Fin (n + 2)) :
    GadgetWitness (g.relabelFree (zeroPort i)) := by
  let ports := List.ofFn (Sum.inl : Fin (n + 2) → Fin (n + 2) ⊕ Fin g.numAux)
  let f := Sum.map (zeroPort i) (id : Fin g.numAux → _)
  have hn : ports.Nodup := List.nodup_ofFn.mpr Sum.inl_injective
  have hout : ((ports.eraseIdx i.val).map f) = List.ofFn Sum.inl :=
    zeroPort_survivors n g.numAux i
  have ht : ((ports.eraseIdx i.val).map f).Nodup := by
    rw [hout]
    exact List.nodup_ofFn.mpr Sum.inl_injective
  by_cases hi : i.val + 1 < n + 2
  · let h := w.identifyAt f i.val (by simpa only [ports, List.length_ofFn] using hi) hn
      (by
        intro a _ b _
        have hnext : (⟨i.val + 1, hi⟩ : Fin (n + 2)) = finRotate (n + 2) i := by
          apply Fin.ext
          rw [val_finRotate]
          change i.val + 1 = if i.val + 1 = n + 2 then 0 else i.val + 1
          split_ifs <;> omega
        simpa only [ports, List.getElem_ofFn, hnext] using
          zeroLabel_kernel n g.numAux i a b) ht
    refine ⟨h.certificate, ?_⟩
    change verify (g.body.relabel f)
      (List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)) h.certificate = true
    rw [← hout]
    exact h.accepted
  · have hilast : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    simp only [Fin.val_last] at hout ht
    let middle := List.ofFn (fun j : Fin n =>
      (Sum.inl j.succ.castSucc : Fin (n + 2) ⊕ Fin g.numAux))
    have hword : ports = (Sum.inl 0 :: middle) ++ [Sum.inl (Fin.last (n + 1))] := by
      change List.ofFn (Sum.inl : Fin (n + 2) → Fin (n + 2) ⊕ Fin g.numAux) = _
      rw [List.ofFn_succ', List.concat_eq_append]
      congr 1
      rw [List.ofFn_succ]
      simp only [Fin.castSucc_zero, middle]
    have herase : ports.eraseIdx (n + 1) = Sum.inl 0 :: middle := by
      rw [hword, List.eraseIdx_append_of_length_le]
      · simp [middle]
      · simp [middle]
    let w' : Witness g.body ((Sum.inl 0 :: middle) ++ [Sum.inl (Fin.last (n + 1))]) :=
      ⟨w.certificate, by rw [← hword]; exact w.accepted⟩
    let h := w'.identifyWrap f (by rw [← hword]; exact hn) (by simp)
      (by
        intro a _ b _
        simpa only [finRotate_last] using
          zeroLabel_kernel n g.numAux (Fin.last (n + 1)) a b)
      (by rw [← herase]; exact ht)
    refine ⟨h.certificate, ?_⟩
    change verify (g.body.relabel f)
      (List.ofFn (Sum.inl : Fin (n + 1) → Fin (n + 1) ⊕ Fin g.numAux)) h.certificate = true
    rw [← hout, herase]
    exact h.accepted

end Cslib.Complexity.CSP.OrderedBoundary
