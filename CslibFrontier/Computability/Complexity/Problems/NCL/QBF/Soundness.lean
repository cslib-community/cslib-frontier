/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Forall

/-!
# The universal quantifier's record invariant

The universal quantifier of [HearnDemaine2005, Lemma 4] must remember that its suffix was
satisfied with the value `false`. A record refers to the current assignment of the preceding
variables, called the context here. The context may change while the quantifier is inactive;
it must be frozen during a try. Thus a fixed proposition saying that the false branch once
succeeded would not suffice.

For an occurrence of the quantifier in any containing diagram, the invariant says that a set
record certifies the false branch in the current context. When the record is first set, the
suffix is satisfied with the value `false`. While it remains set, the quantifier needs trying
in, so the context stays fixed. These two cases prove preservation under each move, including
moves outside the occurrence. Induction along a path replaces the paper's historical argument.

The final theorem assumes soundness of the suffix only at reachable configurations. In a chain
of quantifiers this is the induction hypothesis; freezing of its context follows from the
preceding quantifiers' `mem_eq_of_step` lemmas and propagation of the try signal. This module
does not yet construct the chain or establish those hypotheses for a closed QBF circuit.

## Main definitions

* `Cslib.Complexity.NCL.QBF.ForallGadget.RecordInvariant`: a set record certifies the false
  branch in the current context.

## Main results

* `Cslib.Complexity.NCL.QBF.ForallGadget.recordInvariant_of_reachable`: the record invariant
  is preserved along every reachable path.
* `Cslib.Complexity.NCL.QBF.ForallGadget.forall_of_reachable`: from any legal configuration
  with trying in inactive, satisfied above certifies both branches in the current context.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.ForallGadget

open Diagram

variable {a b : List Color} {D : Diagram Gate a b} (o : Occurrence forallGadget D)
  {α : Type*} (context : (D.Edge → Bool) → α) (P : α → Bool → Prop)

/-- A set record certifies the false branch of the suffix in the current context. -/
@[expose] def RecordInvariant (t : D.Edge → Bool) : Prop :=
  t (o.emb recMem) = true → P (context t) false

private theorem recordInvariant_step {s t : D.Edge → Bool}
    (h : (D.graph Gate.interp).Step s t)
    (hadm : s (o.emb satIn) = false → s (o.emb tryOut) = true)
    (hfreeze : s (o.emb tryIn) = true → context s = context t)
    (hsuffix : s (o.emb satIn) = false → P (context s) (s (o.emb mem)))
    (hs : RecordInvariant o context P s) : RecordInvariant o context P t := by
  obtain ⟨hu, hv, e, rfl⟩ := h
  intro hrec
  by_cases he : e = o.emb recMem
  · subst e
    have hsat := satIn_of_step_recMem (o.legal hu) (o.legal_reverse hv)
    have hmem := mem_of_step_recMem (o.legal hu) (o.legal_reverse hv) hadm
    have hc := hfreeze (tryIn_of_tryOut (o.legal hu) (hadm hsat))
    rw [← hc, ← hmem]
    exact hsuffix hsat
  · have hr : s (o.emb recMem) = true :=
      (reverse_of_ne s (Ne.symm he)).symm.trans hrec
    rw [← hfreeze (tryIn_of_recMem (o.legal hu) hadm hr)]
    exact hs hr

variable {s t : D.Edge → Bool}
    (hadm : ∀ u, (D.graph Gate.interp).Reachable s u →
      u (o.emb satIn) = false → u (o.emb tryOut) = true)
    (hfreeze : ∀ u v, (D.graph Gate.interp).Reachable s u →
      (D.graph Gate.interp).Step u v → u (o.emb tryIn) = true → context u = context v)
    (hsuffix : ∀ u, (D.graph Gate.interp).Reachable s u →
      u (o.emb satIn) = false → P (context u) (u (o.emb mem)))

include hadm hfreeze hsuffix

/-- The record invariant holds along every reachable path, assuming that the suffix is sound
at reachable configurations and the context is frozen by moves while trying in. -/
theorem recordInvariant_of_reachable (hs : RecordInvariant o context P s)
    (h : (D.graph Gate.interp).Reachable s t) :
    RecordInvariant o context P t := by
  induction h with
  | refl => exact hs
  | tail hu huv ih =>
    exact recordInvariant_step o context P huv (hadm _ hu) (hfreeze _ _ hu huv) (hsuffix _ hu) ih

/-- **Soundness of a universal quantifier in a containing diagram** [HearnDemaine2005, Lemma 4].
Starting from any legal configuration with trying in inactive, satisfied above certifies both
branches in the current context. The suffix need only be sound at reachable configurations. -/
theorem forall_of_reachable (hs : (D.graph Gate.interp).Legal s)
    (hstart : s (o.emb tryIn) = false)
    (h : (D.graph Gate.interp).Reachable s t) (hsat : t (o.emb satOut) = false) :
    ∀ value, P (context t) value := by
  have ht := o.legal (h.legal hs)
  have hinit : RecordInvariant o context P s := fun hr =>
    Bool.noConfusion (hstart.symm.trans (tryIn_of_recMem (o.legal hs) (hadm _ .refl) hr))
  have hrec := recordInvariant_of_reachable o context P hadm hfreeze hsuffix hinit h
  intro value
  cases value with
  | false => exact hrec (recMem_of_satOut ht (hadm _ h) hsat)
  | true =>
    have hm := mem_of_satOut ht (hadm _ h) hsat
    change t (o.emb mem) = true at hm
    simpa only [hm] using hsuffix t h (satIn_of_satOut ht hsat)

end Cslib.Complexity.NCL.QBF.ForallGadget
