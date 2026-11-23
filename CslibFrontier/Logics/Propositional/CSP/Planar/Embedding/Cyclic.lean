/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ScopeReindex
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryRotateProgram
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScopeIndex
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Symbols
import CslibFrontier.Foundations.GroupTheory.Perm.Fin
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Cyclic transport of actual ordered boundaries

The structural probe is reindexed by the opposite cyclic shift, preserving the original
clockwise argument rotations. The source and target actual bodies are identical. Numerical
genus and complete target certificate acceptance follow internally from occurrence transport
and probe removal. The distinct-boundary guard is explicit; closed components and nullaries
remain present, including at arity zero. These are original finite structural constructions.

## Main results

* `Witness.unrotateOfFn_certificate`: the complete RIGHT table, with its original premises.
* `Witness.rotateOfFn_certificate`: the complete static output table is the literal
  forward cyclic reindex program, including exact short-boundary identity.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

private noncomputable def reindexOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup)
    (p q : Equiv.Perm (Fin n))
    (hq : ∀ j, q (finRotate n j) = finRotate n (q j))
    (hrev : ∀ j, (q j).rev = p j.rev) : Witness F (List.ofFn (v ∘ p)) := by
  let B := F.map (fun c => Constraint.mk (some c.rel) c.scope)
  let scope : Fin n → V := fun j => v j.rev
  have hs :
      verifyRotationCertificate (B ++ [Constraint.mk none (List.ofFn scope)]) w.certificate =
        true := by
    simpa only [B, scope, probeBody, List.reverse_ofFn] using w.probe_accepted
  have he := (verifyRotationCertificate_eq_true_iff _ _).mp hs
  have hrot := he.choose
  let certificate := reindexLastScopeCertificate B none scope q w.certificate hrot
  have ht := verifyRotationCertificate_reindexLastScopeCertificate B none scope q hq
    w.certificate hrot hs
  have hscope : scope ∘ q = fun j => v (p j.rev) := by
    funext j
    exact congrArg v (hrev j)
  have hout : verifyRotationCertificate (probeBody F (List.ofFn (v ∘ p)))
      certificate = true := by
    simpa only [B, hscope, probeBody, List.reverse_ofFn, Function.comp_apply] using ht
  have hv : Function.Injective v := List.nodup_ofFn.mp hn
  have hn' : (List.ofFn (v ∘ p)).Nodup := List.nodup_ofFn.mpr (hv.comp p.injective)
  exact Witness.ofProbe hn' certificate hout

/-- Cyclically shift a distinct named boundary one step forwards, retaining the literal
body. The probe uses the opposite directed shift, not a reflected argument rotation. -/
noncomputable def Witness.rotateOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    Witness F (List.ofFn (v ∘ finRotate n)) :=
  reindexOfFn w hn (finRotate n) (finRotate n).symm (by
    intro j
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]) (by
      intro j
      have := j.neZero
      rw [finRotate_symm_apply, Fin.rev_sub, finRotate_apply])

/-- Cyclically shift a distinct named boundary one step backwards. Arity zero and one,
unused ports, arbitrary body degree and closed components need no separate provider. -/
noncomputable def Witness.unrotateOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    Witness F (List.ofFn (v ∘ (finRotate n).symm)) :=
  reindexOfFn w hn (finRotate n).symm (finRotate n) (by intro j; rfl) (by
    intro j
    have := j.neZero
    rw [finRotate_apply, Fin.rev_add, finRotate_symm_apply])

section

open Cslib.Logic.PL.CSP

private theorem window_coordinates (M N : ℕ) (shift : ℕ → ℕ) :
    (∀ i, i < 2 * M → boundaryIndexMap M N shift i = i) ∧
      (∀ (j : Fin N) (b : Bool), boundaryIndexMap M N shift
        (2 * (M + j.val) + b.toNat) = 2 * (M + shift j.val) + b.toNat) := by
  unfold boundaryIndexMap
  constructor
  · intro i hi
    rw [ite_eq_right (by omega)]
  · intro j b
    have hw : 2 * M ≤ 2 * (M + j.val) + b.toNat ∧
        2 * (M + j.val) + b.toNat < 2 * (M + N) := by
      have := j.isLt
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hd : (2 * (M + j.val) + b.toNat) / 2 - M = j.val := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hb : (2 * (M + j.val) + b.toNat) % 2 = b.toNat := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    rw [ite_eq_left hw, hd, hb]

private theorem rotate_mod (n : ℕ) (j : Fin n) :
    (j.val + 1) % n = (finRotate n j).val := by
  rw [val_finRotate]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by have := j.isLt; omega)

private theorem unrotate_mod (n : ℕ) (j : Fin n) :
    (j.val + n - 1) % n = ((finRotate n).symm j).val := by
  rw [val_finRotate_symm]
  split_ifs with h
  · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  · have he : j.val + n - 1 = n + (j.val - 1) := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := j.isLt; omega)]

private theorem scope_index_maps {A : Type} (B : CSP A V) (r : A)
    {n : ℕ} (x : Fin n → V) (q : Equiv.Perm (Fin n)) (f b : ℕ → ℕ)
    (hf : ∀ i, i < 2 * B.occurrences.length → f i = i)
    (hb : ∀ i, i < 2 * B.occurrences.length → b i = i)
    (hfp : ∀ (j : Fin n) (side : Bool),
      f (2 * (B.occurrences.length + j.val) + side.toNat) =
        2 * (B.occurrences.length + (q.symm j).val) + side.toNat)
    (hbp : ∀ (j : Fin n) (side : Bool),
      b (2 * (B.occurrences.length + (q.symm j).val) + side.toNat) =
        2 * (B.occurrences.length + j.val) + side.toNat) :
    ∀ (o : (B ++ [Constraint.mk r (List.ofFn x)]).Occurrence) (side : Bool),
      (incidenceDart (reindexLastScopeOccurrenceEquiv B r x q o) side).index =
        f (incidenceDart o side).index ∧
      b (incidenceDart (reindexLastScopeOccurrenceEquiv B r x q o) side).index =
        (incidenceDart o side).index := by
  intro o side
  obtain ⟨u, rfl⟩ := (appendOfFnOccurrenceEquiv B r x).surjective o
  cases u with
  | inl o =>
    rw [reindexLastScopeOccurrenceEquiv_apply]
    change (incidenceDart (appendOfFnOccurrenceEquiv B r (x ∘ q) (Sum.inl o)) side).index =
      f (incidenceDart (appendOfFnOccurrenceEquiv B r x (Sum.inl o)) side).index ∧
      b (incidenceDart (appendOfFnOccurrenceEquiv B r (x ∘ q) (Sum.inl o)) side).index =
        (incidenceDart (appendOfFnOccurrenceEquiv B r x (Sum.inl o)) side).index
    simp only [Dart.index, incidenceDart, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inl]
    have hi : 2 * incidenceEdgeIndex o + side.toNat < 2 * B.occurrences.length := by
      have h := incidenceEdgeIndex_lt o
      rw [incidenceGraph_edges, List.length_map] at h
      cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    exact ⟨(hf _ hi).symm, hb _ hi⟩
  | inr j =>
    rw [reindexLastScopeOccurrenceEquiv_apply]
    change (incidenceDart (appendOfFnOccurrenceEquiv B r (x ∘ q)
      (Sum.inr (q.symm j))) side).index =
      f (incidenceDart (appendOfFnOccurrenceEquiv B r x (Sum.inr j)) side).index ∧
      b (incidenceDart (appendOfFnOccurrenceEquiv B r (x ∘ q)
        (Sum.inr (q.symm j))) side).index =
        (incidenceDart (appendOfFnOccurrenceEquiv B r x (Sum.inr j)) side).index
    simp only [Dart.index, incidenceDart, incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr]
    exact ⟨(hfp j side).symm, hbp j side⟩

private theorem scope_table_reindex {A : Type} (B : CSP A V) (r : A)
    {n : ℕ} (x : Fin n → V) (q : Equiv.Perm (Fin n)) (c : RotationCertificate)
    (hr : RotationCertificate.verifyRotation
      (incidenceGraph (B ++ [Constraint.mk r (List.ofFn x)])) c = true)
    (f b : ℕ → ℕ)
    (hm : ∀ o side,
      (incidenceDart (reindexLastScopeOccurrenceEquiv B r x q o) side).index =
        f (incidenceDart o side).index ∧
      b (incidenceDart (reindexLastScopeOccurrenceEquiv B r x q o) side).index =
        (incidenceDart o side).index) :
    reindexLastScopeCertificate B r x q c hr =
      RotationCertificate.reindex c
        (2 * (incidenceGraph (B ++ [Constraint.mk r (List.ofFn (x ∘ q))])).edges.length) f b := by
  classical
  let G := incidenceGraph (B ++ [Constraint.mk r (List.ofFn x)])
  let H := incidenceGraph (B ++ [Constraint.mk r (List.ofFn (x ∘ q))])
  let e := reindexLastScopeOccurrenceEquiv B r x q
  let ed := occurrenceDartEquiv e
  let source := RotationCertificate.decode G c hr
  let out := reindexLastScopeCertificate B r x q c hr
  let raw := RotationCertificate.reindex c (2 * H.edges.length) f b
  change RotationCertificate.ofRotation (reindexLastScopeRotation B r x q source) = raw
  apply (RotationCertificate.ofRotation_eq_iff _ _).mpr
  refine ⟨RotationCertificate.length_reindex _ _ _ _, ?_⟩
  intro d
  obtain ⟨⟨o, side⟩, ho⟩ := (incidenceDartEquiv _).surjective (ed.symm d)
  have hd : ed (incidenceDart o side) = d := by
    rw [← incidenceDartEquiv_apply (o, side), ho]
    exact ed.apply_symm_apply d
  rw [← hd]
  simp only [ed, occurrenceDartEquiv_apply]
  obtain ⟨⟨p, other⟩, hp⟩ := (incidenceDartEquiv _).surjective
    (source.rotate (incidenceDart o side))
  have hstep : c.successor.getD (incidenceDart o side).index 0 =
      (incidenceDart p other).index := by
    rw [← RotationCertificate.index_decode_rotate hr]
    exact (congrArg Dart.index hp).symm
  have ht := getD_reindexLastScopeCertificate_of_step B r x q c hr
    o p side other hstep
  have hbnd : (incidenceDart (e o) side).index < 2 * H.edges.length :=
    ((Dart.indexEquiv H) (incidenceDart (e o) side)).isLt
  rw [RotationCertificate.getD_reindex _ _ _ _ hbnd, (hm o side).2, hstep]
  calc
    f (incidenceDart p other).index =
        out.successor.getD (incidenceDart (e o) side).index 0 :=
      (ht.trans (hm p other).1).symm
    _ = _ := RotationCertificate.getD_ofRotation _ _

private theorem reindexOfFn_certificate {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup)
    {p q : Equiv.Perm (Fin n)}
    {hq : ∀ j, q (finRotate n j) = finRotate n (q j)}
    {hrev : ∀ j, (q j).rev = p j.rev} (f b : ℕ → ℕ)
    (hf : ∀ i, i < 2 * F.occurrences.length → f i = i)
    (hb : ∀ i, i < 2 * F.occurrences.length → b i = i)
    (hfp : ∀ (j : Fin n) (side : Bool),
      f (2 * (F.occurrences.length + j.val) + side.toNat) =
        2 * (F.occurrences.length + (q.symm j).val) + side.toNat)
    (hbp : ∀ (j : Fin n) (side : Bool),
      b (2 * (F.occurrences.length + (q.symm j).val) + side.toNat) =
        2 * (F.occurrences.length + j.val) + side.toNat) :
    (reindexOfFn w hn p q hq hrev).certificate =
      RotationCertificate.reindex w.certificate (2 * (F.occurrences.length + n)) f b := by
  classical
  let B : CSP (Option Rel) V := F.map (fun c => Constraint.mk (some c.rel) c.scope)
  let x : Fin n → V := fun j => v j.rev
  have hM : B.occurrences.length = F.occurrences.length :=
    congrArg List.length (CSP.occurrences_mapRelation F some)
  have hs : verifyRotationCertificate (B ++ [Constraint.mk none (List.ofFn x)])
      w.certificate = true := by
    simpa only [B, x, probeBody, List.reverse_ofFn] using w.probe_accepted
  let hr := ((verifyRotationCertificate_eq_true_iff _ _).mp hs).choose
  have hcount : 2 * (incidenceGraph
      (B ++ [Constraint.mk none (List.ofFn (x ∘ q))])).edges.length =
        2 * (F.occurrences.length + n) := by
    rw [← RotationCertificate.length_ofRotation
      (reindexLastScopeRotation B none x q (RotationCertificate.decode _ w.certificate hr))]
    change (reindexOfFn w hn p q hq hrev).certificate.successor.length = _
    simpa only [List.length_ofFn] using
      (reindexOfFn w hn p q hq hrev).length_certificate
  have hm := scope_index_maps B none x q f b
    (by simpa only [hM] using hf)
    (by simpa only [hM] using hb)
    (by simpa only [hM] using hfp)
    (by simpa only [hM] using hbp)
  change reindexLastScopeCertificate B none x q w.certificate hr = _
  have ht := scope_table_reindex B none x q w.certificate hr f b hm
  rw [hcount] at ht
  exact ht

private theorem reindexOfFn_short_certificate {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup)
    {p q : Equiv.Perm (Fin n)}
    {hq : ∀ j, q (finRotate n j) = finRotate n (q j)}
    {hrev : ∀ j, (q j).rev = p j.rev} (hshort : n ≤ 1) :
    (reindexOfFn w hn p q hq hrev).certificate = w.certificate := by
  have hj : ∀ j : Fin n, (q.symm j).val = j.val := by
    intro j
    have h₁ := j.isLt
    have h₂ := (q.symm j).isLt
    omega
  have ht := reindexOfFn_certificate (p := p) (q := q) (hq := hq) (hrev := hrev)
    w hn id id (fun _ _ => rfl) (fun _ _ => rfl)
    (by intro j side; simp only [id_eq, hj])
    (by intro j side; simp only [id_eq, hj])
  refine ht.trans ?_
  have hc : w.certificate.successor.length = 2 * (F.occurrences.length + n) := by
    simpa only [List.length_ofFn] using w.length_certificate
  cases hcert : w.certificate with
  | mk values =>
    apply congrArg RotationCertificate.mk
    change (List.range (2 * (F.occurrences.length + n))).map
      (fun i => values.getD i 0) = values
    have hv : values.length = 2 * (F.occurrences.length + n) := by
      simpa only [hcert] using hc
    rw [← hv]
    exact List.map_getD_range _ 0

/-- The existing static LEFT constructor emits the complete raw table.
Only its original witness and boundary-distinctness premise are needed; short tables retain
literal identity and no target rotation, genus or map-agreement provider is input. -/
theorem Witness.rotateOfFn_certificate {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    (w.rotateOfFn hn).certificate =
      rotateBoundaryCertificate F.occurrences.length n w.certificate := by
  unfold Witness.rotateOfFn
  unfold rotateBoundaryCertificate
  by_cases hshort : n ≤ 1
  · rw [ite_eq_left hshort]
    exact reindexOfFn_short_certificate w hn hshort
  · rw [ite_eq_right hshort]
    let M := F.occurrences.length
    let f := boundaryIndexMap M n (fun j => (j + 1) % n)
    let b := boundaryIndexMap M n (fun j => (j + n - 1) % n)
    have hf := window_coordinates M n (fun j => (j + 1) % n)
    have hb := window_coordinates M n (fun j => (j + n - 1) % n)
    apply reindexOfFn_certificate w hn f b
    · exact hf.1
    · exact hb.1
    · intro j side
      have hfi : f (2 * (M + j.val) + side.toNat) =
          2 * (M + ((j.val + 1) % n)) + side.toNat := hf.2 j side
      rw [hfi, rotate_mod]
      rfl
    · intro j side
      change b (2 * (M + (finRotate n j).val) + side.toNat) = _
      have hbi : b (2 * (M + (finRotate n j).val) + side.toNat) =
          2 * (M + (((finRotate n j).val + n - 1) % n)) + side.toNat :=
        hb.2 (finRotate n j) side
      rw [hbi, unrotate_mod, Equiv.symm_apply_apply]

/-- The existing static RIGHT constructor emits the complete raw table.
Only its original witness and boundary-distinctness premise are needed; short tables retain
literal identity and no target rotation, genus or map-agreement provider is input. -/
theorem Witness.unrotateOfFn_certificate {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    (w.unrotateOfFn hn).certificate =
      rotateBoundaryCertificateRight F.occurrences.length n w.certificate := by
  unfold Witness.unrotateOfFn
  rw [rotateBoundaryCertificateRight_eq_reindex_mod]
  by_cases hshort : n ≤ 1
  · rw [ite_eq_left hshort]
    exact reindexOfFn_short_certificate w hn hshort
  · rw [ite_eq_right hshort]
    let M := F.occurrences.length
    let f := boundaryIndexMap M n (fun j => (j + n - 1) % n)
    let b := boundaryIndexMap M n (fun j => (j + 1) % n)
    have hf := window_coordinates M n (fun j => (j + n - 1) % n)
    have hb := window_coordinates M n (fun j => (j + 1) % n)
    apply reindexOfFn_certificate w hn f b
    · exact hf.1
    · exact hb.1
    · intro j side
      have hfi : f (2 * (M + j.val) + side.toNat) =
          2 * (M + ((j.val + n - 1) % n)) + side.toNat := hf.2 j side
      rw [hfi, unrotate_mod]
    · intro j side
      change b (2 * (M + ((finRotate n).symm j).val) + side.toNat) = _
      have hbi : b (2 * (M + ((finRotate n).symm j).val) + side.toNat) =
          2 * (M + ((((finRotate n).symm j).val + 1) % n)) + side.toNat :=
        hb.2 ((finRotate n).symm j) side
      rw [hbi, rotate_mod, Equiv.apply_symm_apply]


end

end Cslib.Complexity.CSP.OrderedBoundary
