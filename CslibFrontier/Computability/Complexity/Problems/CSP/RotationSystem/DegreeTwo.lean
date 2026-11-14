/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateTransport
import Mathlib.Data.Finset.Card

/-!
# Uniqueness of ordered incidence rotations at variable degree at most two

Argument order fixes every constraint-side rotation. At a variable with one or two incident
darts, the single-cycle condition fixes its rotation too. Thus the whole ordered rotation,
and every accepted raw table for it, is unique. Constraint arities remain unrestricted.

This is a uniqueness result, not an existence or numerical genus-zero theorem. Its degree
guard is useful for inspecting literal tables of radial gadgets, without restricting the
general gadget and normalization APIs.

## Main results

* `rotation_eq_of_variable_degree_le_two`: uniqueness of the prescribed ordered rotation.
* `rotationCertificate_eq_of_variable_degree_le_two`: equality of accepted literal tables.
-/

public section

namespace Cslib.Complexity.CSP

open Graph

variable {Rel V : Type} [DecidableEq V] {F : Cslib.Logic.PL.CSP Rel V}

/-- Ordered incidence rotations are unique if each variable-side endpoint fiber has at
most two darts. Only variable fibers have a degree guard; constraint arities are arbitrary.
No numerical genus hypothesis is used. -/
theorem rotation_eq_of_variable_degree_le_two
    (hdegree : ∀ d : Dart (incidenceGraph F), d.2 = false →
      (Finset.univ.filter fun e : Dart (incidenceGraph F) => e.vertex = d.vertex).card ≤ 2)
    (r s : RotationSystem (incidenceGraph F))
    (hr : RespectsArgumentOrder r) (hs : RespectsArgumentOrder s) : r = s := by
  have hp : r.rotate = s.rotate := by
    apply Equiv.ext
    intro d
    cases hside : d.2 with
    | true =>
      obtain ⟨o, ho⟩ := exists_incidenceDart d
      rw [hside] at ho
      rw [← ho, hr o, hs o]
    | false =>
      by_cases hrfix : r.rotate d = d
      · have hcycle := (r.sameCycle_iff d (s.rotate d)).mpr (s.vertex_rotate d).symm
        exact hrfix.trans (hcycle.eq_of_left hrfix)
      by_cases hsfix : s.rotate d = d
      · have hcycle := (s.sameCycle_iff d (r.rotate d)).mpr (r.vertex_rotate d).symm
        exact (hcycle.eq_of_left hsfix).symm.trans hsfix.symm
      by_contra hne
      have hsubset : {d, r.rotate d, s.rotate d} ⊆
          Finset.univ.filter (fun e : Dart (incidenceGraph F) => e.vertex = d.vertex) := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl <;> simp [r.vertex_rotate, s.vertex_rotate]
      have hc := Finset.card_le_card hsubset
      have hb := hdegree d hside
      have hthree : ({d, r.rotate d, s.rotate d} : Finset (Dart (incidenceGraph F))).card = 3 := by
        exact Finset.card_eq_three.mpr
          ⟨d, r.rotate d, s.rotate d, Ne.symm hrfix, Ne.symm hsfix, hne, rfl⟩
      rw [hthree] at hc
      omega
  cases r
  cases s
  cases hp
  rfl

/-- A valid raw rotation table with the prescribed argument order is determined by its
actual body when all variable endpoint fibers have size at most two. Neither table is
assumed to have numerical genus zero. -/
theorem rotationCertificate_eq_of_variable_degree_le_two
    (hdegree : ∀ d : Dart (incidenceGraph F), d.2 = false →
      (Finset.univ.filter fun e : Dart (incidenceGraph F) => e.vertex = d.vertex).card ≤ 2)
    {c d : RotationCertificate}
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (hd : RotationCertificate.verifyRotation (incidenceGraph F) d = true)
    (hco : verifyArgumentOrder F c = true) (hdo : verifyArgumentOrder F d = true) : c = d := by
  have he := rotation_eq_of_variable_degree_le_two hdegree
    (RotationCertificate.decode _ _ hc) (RotationCertificate.decode _ _ hd)
    ((verifyArgumentOrder_eq_true_iff hc).mp hco) ((verifyArgumentOrder_eq_true_iff hd).mp hdo)
  rw [← RotationCertificate.ofRotation_decode hc,
    ← RotationCertificate.ofRotation_decode hd, he]

end Cslib.Complexity.CSP
