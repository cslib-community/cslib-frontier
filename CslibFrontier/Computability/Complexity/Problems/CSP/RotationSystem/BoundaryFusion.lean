/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CrossInsertion
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentify
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Executed fusion of the first two boundary wires

The raw program identifies the second boundary name with the first throughout the actual
body, removes the first structural marker, and retains the mapped tail in its original
clockwise order. It executes the existing outgoing swap and bounded prefix restriction.
With fewer than two positions it returns the input unchanged. Repeated names and malformed
tables remain raw data; acceptance is required only for checker correctness.

This original wire operation is a step toward the common-complement CROSS compiler in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091). Positioned fusion,
hiding the remaining seam, cyclic transport, transposition and accumulated polynomial
bounds are not established here. This module makes no native runtime assertion.

## Main definitions

* `CrossInsertion.fuseHead`: execute one boundary-wire identification on raw states.

## Main results

* `CrossInsertion.accepted_fuseHead`: full checker preservation for the computed table.
* `CrossInsertion.eval_fuseHead_iff`: exact quotient-assignment extension semantics.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary

variable {Rel : Type}

/-- Fuse the first two distinct boundary wires by updating the second name to the first.
The first marker is removed; its mapped successor survives. Short inputs are unchanged. -/
@[expose] def fuseHead (I : State Rel) : State Rel :=
  match I.ports with
  | x :: y :: ps =>
    let f := Function.update id y x
    ⟨I.body.relabel f, (y :: ps).map f,
      equalDropCertificate I.body ps.length I.rotation⟩
  | _ => I

private theorem survivor_nodup {x y : ℕ} {ps : List ℕ} (hn : (x :: y :: ps).Nodup) :
    ((y :: ps).map (Function.update id y x)).Nodup := by
  apply List.Nodup.map_on _ hn.of_cons
  intro a ha b hb he
  rw [Function.update_id_apply_eq_iff] at he
  rcases he with he | ⟨rfl, _⟩ | ⟨_, rfl⟩
  · exact he
  · exact ((List.nodup_cons.mp hn).1 ha).elim
  · exact ((List.nodup_cons.mp hn).1 hb).elim

/-- The general boundary constructor's exact-table equation proves acceptance of this raw
program. No target witness, rotation, genus or runtime premise is supplied. -/
theorem accepted_fuseHead (I : State Rel) (hI : I.Accepted) : (fuseHead I).Accepted := by
  rcases I with ⟨F, ports, c⟩
  cases ports with
  | nil => exact hI
  | cons x ports =>
    cases ports with
    | nil => exact hI
    | cons y ps =>
      let v : Fin (ps.length + 2) → ℕ := Fin.cons x (Fin.cons y ps.get)
      let f := Function.update id y x
      have hv : List.ofFn v = x :: y :: ps := by
        rw [List.ofFn_cons, List.ofFn_cons, List.ofFn_get]
      have ht : List.ofFn (fun i : Fin (ps.length + 1) => f (v i.succ)) =
          (y :: ps).map f := by
        simp [v]
      have hn := hI.1
      have hxy : x ≠ y := by
        intro he
        exact (List.nodup_cons.mp hn).1 (by simp [he])
      let w : Witness F (List.ofFn v) := ⟨c, by rw [hv]; exact hI.2⟩
      have hk : ∀ a ∈ F.vars ++ List.ofFn v, ∀ b ∈ F.vars ++ List.ofFn v,
          f a = f b ↔ Function.update id (v 1) (v 0) a =
            Function.update id (v 1) (v 0) b := by
        intro a _ b _
        rfl
      have htail : (List.ofFn (fun i : Fin (ps.length + 1) => f (v i.succ))).Nodup := by
        rw [ht]
        exact survivor_nodup hn
      let out := w.identifyFirstTwoOfFn f hxy hk htail
      have hc := w.identifyFirstTwoOfFn_certificate f hxy hk htail
      have h := out.accepted
      change OrderedBoundary.verify (F.relabel f)
        (List.ofFn (fun i : Fin (ps.length + 1) => f (v i.succ))) out.certificate = true at h
      rw [hc, ht] at h
      exact ⟨survivor_nodup hn, h⟩

/-- A fused satisfying assignment is exactly a source assignment equating the selected
pair and agreeing on every other natural name, including all unused names. This statement
needs neither a source checker nor source arity assumption. -/
theorem eval_fuseHead_iff (sem : Rel → List Bool → Bool) (F : CSP Rel ℕ)
    (x y : ℕ) (ps : List ℕ) (c : Graph.RotationCertificate) (hxy : x ≠ y)
    (σ : ℕ → Bool) :
    (fuseHead (⟨F, x :: y :: ps, c⟩ : State Rel)).body.eval sem σ = true ↔
      ∃ τ : ℕ → Bool, F.eval sem τ = true ∧ τ x = τ y ∧
        ∀ z, z ≠ y → τ z = σ z := by
  rw [fuseHead, CSP.eval_relabel]
  constructor
  · intro h
    refine ⟨σ ∘ Function.update id y x, h, ?_, ?_⟩
    · simp [hxy]
    · intro z hz
      simp [hz]
  · rintro ⟨τ, ht, he, hagree⟩
    have hassign : σ ∘ Function.update id y x = τ := by
      funext z
      by_cases hz : z = y
      · subst z
        simpa only [Function.comp_apply, Function.update_self] using
          (hagree x hxy).symm.trans he
      · simpa only [Function.comp_apply, Function.update_of_ne hz, id_eq]
          using (hagree z hz).symm
    rw [hassign]
    exact ht

end Cslib.Complexity.CSP.CrossInsertion
