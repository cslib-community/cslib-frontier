/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossInsertion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe

/-!
# Executed hiding of the first boundary marker

`CrossInsertion.hideHead` keeps the entire original body and removes only its first
structural boundary marker. The table is the existing list-funded prefix restriction.
Hiding makes that port existential in the ordered boundary assignment relation; it neither
removes a body occurrence nor renames a variable. Unused ports and closed or nullary body
components are retained. An empty raw boundary returns the exact input unchanged.

This original composition step is one prerequisite for the CROSS compiler in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091). Positioned operations,
cyclic transport, transposition and accumulated iteration bounds remain open there.

## Main definitions

* `CrossInsertion.hideHead`: remove one structural marker on raw states.

## Main results

* `CrossInsertion.accepted_hideHead`: the literal computed table passes both full checks.
* `CrossInsertion.boundary_hideHead_iff`: exact ordered existential projection of assignments.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary

variable {Rel : Type}

/-- Hide the first boundary position, retaining the same body and inherited tail order.
The raw table is restricted to the body and remaining probe darts. Empty inputs are identity. -/
@[expose] def hideHead (I : State Rel) : State Rel :=
  match I.ports with
  | [] => I
  | _ :: ps =>
    ⟨I.body, ps, restrictPrefix (2 * (I.body.occurrences.length + ps.length)) I.rotation⟩

private theorem hideHead_body (I : State Rel) : (hideHead I).body = I.body := by
  rcases I with ⟨F, ports, c⟩
  cases ports <;> rfl

/-- Source acceptance internally supplies the full checker result for the executed
restriction. The original body, including every closed and nullary component, is unchanged. -/
theorem accepted_hideHead (I : State Rel) (hI : I.Accepted) : (hideHead I).Accepted := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => exact hI
  | cons p ps =>
    let w : Witness F (p :: ps) := ⟨c, hI.2⟩
    refine ⟨hI.1.of_cons, ?_⟩
    have h := (w.forgetHead hI.1.of_cons).accepted
    rw [Witness.forgetHead_certificate] at h
    exact h

/-- The surviving ordered boundary values extend by exactly one existential first value.
The same global assignment satisfies the whole body on both sides, including unused names.
This semantic statement also applies to repeated raw boundary names and malformed tables. -/
theorem boundary_hideHead_iff (sem : Rel → List Bool → Bool) (F : CSP Rel ℕ)
    (p : ℕ) (ps : List ℕ) (c : Graph.RotationCertificate) (values : List Bool) :
    (∃ σ : ℕ → Bool,
      (hideHead (⟨F, p :: ps, c⟩ : State Rel)).body.eval sem σ = true ∧
      (hideHead (⟨F, p :: ps, c⟩ : State Rel)).ports.map σ = values) ↔
      ∃ b : Bool, ∃ σ : ℕ → Bool,
        F.eval sem σ = true ∧ (p :: ps).map σ = b :: values := by
  simp only [hideHead_body]
  change (∃ σ : ℕ → Bool, F.eval sem σ = true ∧ ps.map σ = values) ↔ _
  constructor
  · rintro ⟨σ, hσ, hvalues⟩
    exact ⟨σ p, σ, hσ, by rw [List.map_cons, hvalues]⟩
  · rintro ⟨b, σ, hσ, hvalues⟩
    exact ⟨σ, hσ, (List.cons.inj hvalues).2⟩

end Cslib.Complexity.CSP.CrossInsertion
