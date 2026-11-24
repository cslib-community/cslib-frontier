/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Data.List.OfFn

/-!
# Structurally encoded H-word instances

The fixed alphabet is encoded by unary finite ranks. An instance contains two framed lists;
acceptance requires equal lengths, a legal initial word, and its reconfiguration to the target.

## Main definitions

* `HWord.Instance`: initial and target words over one fixed alphabet.
* `HWord.encWord`, `HWord.encInstance`: standard framed encodings.
* `HWord.language`: list-input reachability using the finite-vector game semantics.

## Main results

* `HWord.language_ofFn`: the list problem agrees with the finite-vector semantics.

## References

* [M. Wrochna, *Reconfiguration in bounded bandwidth and treedepth*][Wrochna2014], Section 3.
-/

public section

namespace Cslib.Complexity.NCL.HWord

open _root_.Turing.MultiTapeTM

/-- Two words over a fixed finite alphabet. -/
structure Instance (q : ℕ) where
  /-- The initial word. -/
  source : List (Fin q)
  /-- The target word. -/
  target : List (Fin q)

/-- A framed list of unary ranks in the fixed finite alphabet. -/
abbrev encWord (q : ℕ) : List (Fin q) ↪ List Bool := encList (encFinEnum (Fin q))

/-- Frame the initial and target words as the two fields of the instance. -/
enc_structure encInstance (q : ℕ) : Instance q where
  source : (encWord q), target : (encWord q)

/-- Reconfiguration between equally long words, starting at a legal H-word. -/
@[expose] def language {q : ℕ} (H : Digraph (Fin q)) : Set (Instance q) :=
  {x | ∃ t : Fin x.source.length → Fin q,
    List.ofFn t = x.target ∧ Legal H x.source.get ∧ Reachable H x.source.get t}

/-- List inputs obtained from finite words retain their legality and reachability semantics. -/
theorem language_ofFn {q n : ℕ} (H : Digraph (Fin q)) (s t : Fin n → Fin q) :
    Instance.mk (List.ofFn s) (List.ofFn t) ∈ language H ↔ Legal H s ∧ Reachable H s t := by
  let accepts : (Σ m, Fin m → Fin q) → Prop := fun ⟨m, u⟩ =>
    ∃ v : Fin m → Fin q, List.ofFn v = List.ofFn t ∧ Legal H u ∧ Reachable H u v
  change accepts ⟨(List.ofFn s).length, (List.ofFn s).get⟩ ↔ _
  have he : (⟨(List.ofFn s).length, (List.ofFn s).get⟩ : Σ m, Fin m → Fin q) = ⟨n, s⟩ :=
    List.ofFn_inj'.mp (List.ofFn_get _)
  rw [he]
  simp only [accepts, List.ofFn_inj, exists_eq_left]

end Cslib.Complexity.NCL.HWord
