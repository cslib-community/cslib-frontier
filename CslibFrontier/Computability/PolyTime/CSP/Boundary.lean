/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native restriction of a raw ordered-boundary table

The retained dart count is computed in unary. The supplied table, its entries and all
successor lookups remain binary. Each first-return search uses only the actual table length;
malformed entries do not fund a loop. The certificate applies without a checker invariant.

## Main results

* `computableInPolyTime_restrictPrefix`: plain captured polynomial time for the existing
  literal restriction program, with a computed unary retained count.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Graph Turing.MultiTapeTM

/-- Restrict a computed binary successor table at a computed unary dart count in native
polynomial time. Only the retained count and the actual table length fund the scans;
there is no validity or entry-bound premise. -/
theorem computableInPolyTime_restrictPrefix {α : Type} {input : α ↪ List Bool}
    {table : α → RotationCertificate} {count : α → ℕ}
    (hc : ComputableInPolyTime table input encRotationCertificate)
    (hn : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun a => restrictPrefix (count a) (table a))
      input encRotationCertificate := by
  have hbound : ComputableInPolyTime count input encNat :=
    ComputableInPolyTime.unary_to_binary.comp hn
  apply encRotationCertificate_mk_polyTime
  apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
  apply ComputableInPolyTime.optionGetDWithInput _ (ComputableInPolyTime.const 0)
  apply ComputableInPolyTime.findWithInput
  · apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
    fun_prop
  · fun_prop

end Cslib.Complexity.CSP.OrderedBoundary
