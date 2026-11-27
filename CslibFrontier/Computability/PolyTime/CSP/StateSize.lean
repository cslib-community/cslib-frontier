/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossInsertion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith

/-!
# Encoding bounds for raw boundary states

The component lower bounds and cubic envelope use the existing binary State encoding.
Relation-symbol payload is counted in its supplied encoding, including for infinite
alphabets. These original bounds are shared by the schedule and metadata-run driver;
no validity or runtime premise is part of either statement.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion.State

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM Cslib.BitString

variable {Rel : Type}

/-- The framed State word funds rows, ports, raw table length, relation payload and
every binary body/port name. No checker hypothesis is needed. -/
theorem component_size_le_encoding (encRel : Rel ↪ List Bool) (I : State Rel) :
    let S := (encState encRel I).length
    I.body.length ≤ S ∧ I.ports.length ≤ S ∧ I.rotation.successor.length ≤ S ∧
      ((I.body.map Constraint.rel).map (fun r => (encRel r).length)).sum ≤ S ∧
      ∀ z ∈ I.body.vars ++ I.ports, z.size ≤ S := by
  dsimp only
  have hb : (encCSP encRel encNat I.body).length ≤ (encState encRel I).length := by
    enc_len [encState_apply, encStateFields]
  have hp : (encList encNat I.ports).length ≤ (encState encRel I).length := by
    enc_len [encState_apply, encStateFields]
  have hc : (encList encNat I.rotation.successor).length ≤ (encState encRel I).length := by
    enc_len [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
      Graph.encRotationCertificateFields]
  refine ⟨(SizedListEncoding.length_le (encA := encConstraint encRel encNat)
    (encL := encCSP encRel encNat) I.body).trans hb,
    (SizedListEncoding.length_le (encA := encNat) (encL := encList encNat) I.ports).trans hp,
      (SizedListEncoding.length_le (encA := encNat) (encL := encList encNat)
      I.rotation.successor).trans hc, ?_, ?_⟩
  · apply le_trans _ hb
    calc
      ((I.body.map Constraint.rel).map (fun r => (encRel r).length)).sum =
          (I.body.map (fun c => (encRel c.rel).length)).sum := by
        simp only [List.map_map, Function.comp_def]
      _ ≤ (I.body.map (fun c => 2*(encConstraint encRel encNat c).length+1)).sum := by
        apply List.sum_le_sum
        intro c _
        enc_len [encConstraint_apply]
      _ = (encCSP encRel encNat I.body).length := by
        simp only [encCSP, length_encList]
  · intro z hz
    rw [← Nat.size_eq_bits_len]
    change (encNat z).length ≤ _
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨c, hm, hv⟩ := List.mem_flatMap.mp hz
      have hm' := SizedListEncoding.length_elem_le
        (encA := encConstraint encRel encNat) (encL := encCSP encRel encNat) I.body c hm
      have hv' := SizedListEncoding.length_elem_le
        (encA := encNat) (encL := encList encNat) c.scope z hv
      have hs : (encList encNat c.scope).length ≤ (encConstraint encRel encNat c).length := by
        enc_len [encConstraint_apply]
      exact hv'.trans (hs.trans (hm'.trans hb))
    · exact (SizedListEncoding.length_elem_le
        (encA := encNat) (encL := encList encNat) I.ports z hz).trans hp

/-- Component counts, actual encoded relation payload and binary widths give a cubic
bound for the existing State word, without a finite alphabet or table-validity premise. -/
theorem encoding_length_le (encRel : Rel ↪ List Bool) (J : State Rel) (L : ℕ)
    (hq : J.body.length ≤ L) (hm : J.body.occurrences.length ≤ L)
    (hp : J.ports.length ≤ L) (hd : J.rotation.successor.length ≤ L)
    (hr : ((J.body.map Constraint.rel).map (fun r => (encRel r).length)).sum ≤ L)
    (hw : ∀ z ∈ J.body.vars ++ J.ports, z.size ≤ L)
    (hv : ∀ v ∈ J.rotation.successor, v.size ≤ L) :
    (encState encRel J).length ≤ 64*(L+1)^3 := by
  have hrow (c : Constraint Rel ℕ) (hc : c ∈ J.body) :
      (encConstraint encRel encNat c).length ≤ 2*L+1+L*(2*L+1) := by
    have hrel : (encRel c.rel).length ≤ L := by
      have hx : (encRel c.rel).length ≤
          ((J.body.map Constraint.rel).map (fun r => (encRel r).length)).sum :=
        List.le_sum_of_mem (List.mem_map.mpr
          ⟨c.rel, List.mem_map.mpr ⟨c,hc,rfl⟩,rfl⟩)
      exact hx.trans hr
    have hn : c.scope.length ≤ L := by
      have hx := List.le_sum_of_mem (List.mem_map.mpr ⟨c,hc,rfl⟩ :
        c.scope.length ∈ J.body.map (fun d => d.scope.length))
      have hx' : c.scope.length ≤ J.body.occurrences.length := by
        simpa only [CSP.length_occurrences] using hx
      exact hx'.trans hm
    have hs := length_encList_le encNat c.scope (fun z hz => by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact hw z (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c,hc,hz⟩)))
    rw [encConstraint_apply, length_encPair]
    nlinarith
  have hb := length_encList_le (encConstraint encRel encNat) J.body hrow
  have hports := length_encList_le encNat J.ports (fun z hz => by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact hw z (List.mem_append_right _ hz))
  have htable := length_encList_le encNat J.rotation.successor (fun v hm => by
    rw [encNat_apply, Nat.size_eq_bits_len]; exact hv v hm)
  simp only [encState_apply, encStateFields, Graph.encRotationCertificate_apply,
    Graph.encRotationCertificateFields, length_encPair]
  nlinarith [Nat.mul_le_mul_right (2*(2*L+1+L*(2*L+1))+1) hq,
    Nat.mul_le_mul_right (2*L+1) hp, Nat.mul_le_mul_right (2*L+1) hd]

end Cslib.Complexity.CSP.CrossInsertion.State
