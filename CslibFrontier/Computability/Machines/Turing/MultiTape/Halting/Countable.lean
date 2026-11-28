/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
public import Mathlib.SetTheory.Cardinal.Continuum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-!
# There are countably many decidable sets and computable functions

A machine with finitely many states is determined, up to renaming its states, by its description
(`Turing.MultiTapeTM.Universal.desc`), and descriptions are encoded injectively as bit words
(`Turing.MultiTapeTM.Universal.eDesc`). A machine computes at most one output on each input, so a
computable function is determined by the description of a machine computing it, and there are
countably many computable functions (`Turing.MultiTapeTM.countable_setOf_isComputable`), while
there are continuum many functions from bit strings to bit strings. A decidable set is the set
where some computable Boolean function is `true`, so there are also countably many decidable sets
(`Turing.MultiTapeTM.countable_setOf_isDecidable`).

## Main results

* `Turing.MultiTapeTM.computes_true_iff`: a machine deciding a set halts with output `[true]`
  exactly on its members.
* `Turing.MultiTapeTM.countable_setOf_isComputable`: there are countably many computable
  functions, for all encodings of inputs and outputs.
* `Turing.MultiTapeTM.countable_setOf_isDecidable`: there are countably many decidable sets, for
  every encoding.
* `Turing.MultiTapeTM.countable_setOf_isComputable_and_mk_eq_continuum`: Goldreich, Theorem 1.4;
  the computable functions on bit strings are countable, all functions form a continuum.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Theorem 1.4
  (draft `r1.pdf` of 30 December 2006, PDF p. 54, printed p. 29).
-/

public section

namespace Turing.MultiTapeTM

open Universal

variable {α : Type*} {enc : α ↪ List Bool}

/-- A machine computing a Boolean function `f` halts with output `[true]` exactly where `f` is
`true`. -/
theorem computes_true_iff {k : ℕ} {State : Type*} {tm : MultiTapeTM k Bool State} {f : α → Bool}
    (htm : ∀ a, tm.Computes (enc a) [f a]) (a : α) : tm.Computes (enc a) [true] ↔ f a = true :=
  ⟨fun h => List.singleton_inj.mp (h.unique (htm a)) |>.symm, fun h => h ▸ htm a⟩

/-- **There are countably many computable functions**, for all encodings of their inputs and
outputs: a computable function is determined by the description of a machine computing it, since
a machine computes at most one output on each input and the output encoding is injective. -/
theorem countable_setOf_isComputable {β : Type*} (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : {f : α → β | IsComputable f encIn encOut}.Countable := by
  have : Countable Desc := eDesc.injective.countable
  have hdesc : ∀ f : {f : α → β // IsComputable f encIn encOut}, ∃ (k : ℕ) (State : Type)
      (_ : Fintype State) (tm : MultiTapeTM k Bool State),
      (∀ a, tm.Computes (encIn a) (encOut (f.1 a))) := fun ⟨f, hf⟩ => by
    obtain ⟨k, State, hfinite, tm, htm⟩ := isComputable_iff.mp hf
    exact ⟨k, State, Fintype.ofFinite State, tm, htm⟩
  choose k State hfin tm htm using hdesc
  let e f : State f ↪ ℕ := (Fintype.equivFin (State f)).toEmbedding.trans Fin.valEmbedding
  let D f := desc (e f) eBit (tm f)
  have hD : Function.Injective D := fun f g hfg => by
    refine Subtype.ext (funext fun a => encOut.injective ?_)
    have hg := (Desc.computes_desc (e g) eBit (tm g) _ _).mpr (htm g a)
    change (D g).Computes _ _ at hg
    rw [← hfg, Desc.computes_desc] at hg
    exact (htm f a).unique hg
  exact Set.countable_coe_iff.mp hD.countable

/-- **There are countably many decidable sets**: a decidable set is the set where some computable
Boolean function is `true`. -/
theorem countable_setOf_isDecidable (enc : α ↪ List Bool) :
    {A : Set α | IsDecidable A enc}.Countable := by
  refine ((countable_setOf_isComputable enc encBool).image fun f => {a | f a = true}).mono ?_
  intro A hA
  obtain ⟨f, hf, hA⟩ := isDecidable_iff.mp hA
  exact ⟨f, hf, Set.ext fun a => (hA a).symm⟩

/-- **On the scarcity of computable functions** [Goldreich, Theorem 1.4][Goldreich2008]: the
functions from bit strings to bit strings computable by a native machine form a countable set,
whereas the set of all such functions has the cardinality of the continuum. -/
theorem countable_setOf_isComputable_and_mk_eq_continuum :
    {f : List Bool → List Bool | IsComputable f encBits encBits}.Countable ∧
      Cardinal.mk (List Bool → List Bool) = Cardinal.continuum := by
  refine ⟨countable_setOf_isComputable encBits encBits, ?_⟩
  rw [← Cardinal.power_def, Cardinal.mk_eq_aleph0 (List Bool), Cardinal.aleph0_power_aleph0]

end Turing.MultiTapeTM
