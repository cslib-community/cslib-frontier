/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AdjacentIdentification
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScopeIndex
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Symbols
import CslibFrontier.Foundations.Data.List.OfFnPositions
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScope
import CslibFrontier.Tactic.FinIndex

/-!
# Adjacent identification on actual ordered boundary words

The first two distinct boundary labels supply cofacial corners through consecutive actual
probe arguments. Their precise selected-pair kernel is imposed on the actual body and
boundary labels. The first duplicate marker is deleted, retaining the survivor order.
No boundary label needs an occurrence in the unaugmented body.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Literal adjacent-equality table program: swap the last probe corner with the
predecessor of the penultimate probe end, then remove the last probe edge. The clocks
are the actual body/boundary counts and supplied table length, never an encoded label.
The residual arity `n` is a static parameter; no uniform binary-arity runtime bound is claimed. -/
@[expose] def equalDropCertificate {V : Type} (F : CSP Rel V) (n : ℕ)
    (c : RotationCertificate) : RotationCertificate :=
  restrictPrefix (2 * (F.occurrences.length + (n + 1)))
    (c.swapSuccessors (2 * (F.occurrences.length + n + 1))
      (c.successor.idxOf (2 * (F.occurrences.length + n))))

/-- Identify the first two boundary labels and remove the first marker. The actual body
is exactly relabeled by `f`; the target boundary is precisely the mapped source tail. -/
noncomputable def Witness.identifyFirstTwoOfFn {F : CSP Rel V} {n : ℕ}
    {v : Fin (n + 2) → V} (w : Witness F (List.ofFn v)) (f : V → W)
    (hv : v 0 ≠ v 1)
    (hk : ∀ a ∈ F.vars ++ List.ofFn v, ∀ b ∈ F.vars ++ List.ofFn v,
      f a = f b ↔ Function.update id (v 1) (v 0) a = Function.update id (v 1) (v 0) b)
    (hn : (List.ofFn (fun i : Fin (n + 1) => f (v i.succ))).Nodup) :
    Witness (F.relabel f) (List.ofFn (fun i : Fin (n + 1) => f (v i.succ))) := by
  let B : CSP (Option Rel) V := F.map (fun c => Constraint.mk (some c.rel) c.scope)
  let scope : Fin (n + 2) → V := fun i => v i.rev
  let S : CSP (Option Rel) V := B ++ [Constraint.mk none (List.ofFn scope)]
  let o : S.Occurrence := appendOfFnOccurrenceEquiv B none scope (Sum.inr (Fin.last (n + 1)))
  let p : S.Occurrence := appendOfFnOccurrenceEquiv B none scope (Sum.inr ⟨n, by omega⟩)
  have ho : o.var = v 0 := by
    have he := congrArg (fun record => record.2.2)
      (record_appendOfFnOccurrenceEquiv_inr B none scope (Fin.last (n + 1)))
    change o.var = scope (Fin.last (n + 1)) at he
    rw [he]
    apply congrArg v
    apply Fin.ext
    simp [Fin.rev]
  have hp : p.var = v 1 := by
    have he := congrArg (fun record => record.2.2)
      (record_appendOfFnOccurrenceEquiv_inr B none scope ⟨n, by omega⟩)
    change p.var = scope ⟨n, by omega⟩ at he
    rw [he]
    apply congrArg v
    fin_index
  have hne : o.var ≠ p.var := by rwa [ho, hp]
  have hsucc : argumentSuccessor p = o := by
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr]
    apply congrArg (fun i => appendOfFnOccurrenceEquiv B none scope (Sum.inr i))
    fin_index [val_finRotate]
  have hsource : S = probeBody F (List.ofFn v) := by
    simp only [S, B, scope, probeBody, List.reverse_ofFn]
  have hkernel : ∀ a ∈ S.vars, ∀ b ∈ S.vars,
      f a = f b ↔ Function.update id p.var o.var a = Function.update id p.var o.var b := by
    intro a ha b hb
    rw [ho, hp]
    apply hk
    · simpa only [hsource, vars_probeBody, List.mem_append, List.mem_reverse] using ha
    · simpa only [hsource, vars_probeBody, List.mem_append, List.mem_reverse] using hb
  have hs : verifyRotationCertificate S w.certificate = true := by
    rw [hsource]
    exact w.probe_accepted
  have hrot := ((verifyRotationCertificate_eq_true_iff S w.certificate).mp hs).choose
  let c := identifyConsecutiveCertificate S f o p hne hkernel w.certificate hrot
  have ht := verifyRotationCertificate_identifyConsecutiveCertificate S f o p hne hkernel
    hsucc w.certificate hrot hs
  have hmap : (List.ofFn v).map f =
      f (v 0) :: List.ofFn (fun i : Fin (n + 1) => f (v i.succ)) := by
    rw [List.ofFn_succ, List.map_cons, List.map_ofFn]
    rfl
  have hprobe : verifyRotationCertificate (probeBody (F.relabel f)
      (f (v 0) :: List.ofFn (fun i : Fin (n + 1) => f (v i.succ)))) c = true := by
    rw [← hmap, ← probeBody_relabel, ← hsource]
    exact ht
  exact Witness.ofProbe hn _ (verifyRotationCertificate_restrictPrefix_probe_cons
    (F.relabel f) (f (v 0)) (List.ofFn (fun i : Fin (n + 1) => f (v i.succ))) c hprobe)

/-- The general boundary identification emits the literal outgoing swap and bounded
prefix restriction. Its hypotheses are exactly those of the existing constructor. -/
theorem Witness.identifyFirstTwoOfFn_certificate {F : CSP Rel V} {n : ℕ}
    {v : Fin (n + 2) → V} (w : Witness F (List.ofFn v)) (f : V → W)
    (hv : v 0 ≠ v 1)
    (hk : ∀ a ∈ F.vars ++ List.ofFn v, ∀ b ∈ F.vars ++ List.ofFn v,
      f a = f b ↔ Function.update id (v 1) (v 0) a = Function.update id (v 1) (v 0) b)
    (hn : (List.ofFn (fun i : Fin (n + 1) => f (v i.succ))).Nodup) :
    (w.identifyFirstTwoOfFn f hv hk hn).certificate =
      equalDropCertificate F n w.certificate := by
  unfold Witness.identifyFirstTwoOfFn
  change restrictPrefix _ (identifyConsecutiveCertificate _ _ _ _ _ _ _ _) = _
  rw [identifyConsecutiveCertificate_eq_swapSuccessors]
  simp only [Dart.index, incidenceDart, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr,
    Bool.toNat_false, Nat.add_zero, length_occurrences_probeBody, CSP.occurrences_relabel,
    List.length_map, List.length_ofFn, Fin.val_last, equalDropCertificate,
    CSP.occurrences_mapRelation]
  rfl


end Cslib.Complexity.CSP.OrderedBoundary
