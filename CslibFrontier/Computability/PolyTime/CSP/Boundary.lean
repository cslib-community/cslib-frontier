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
  have hs := RotationCertificate.computableInPolyTime_successor.comp hc
  have hsteps := (ComputableInPolyTime.length_list encNat).comp hs
  have hbound := ComputableInPolyTime.unary_to_binary.comp hn
  have hout : ComputableInPolyTime (fun a => (List.range (count a)).map fun i =>
      (((List.range (table a).successor.length).map fun k =>
        RotationCertificate.walk (table a).successor (k + 1) i).find?
          (fun j => decide (j < count a))).getD 0) input (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput (encA := encUnary)
      (ComputableInPolyTime.range.comp hn)
    have hp := ComputableInPolyTime.fst input encUnary
    have hi := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd input encUnary)
    have hwalks : ComputableInPolyTime (fun p : α × ℕ =>
        (List.range (table p.1).successor.length).map fun k =>
          RotationCertificate.walk (table p.1).successor (k + 1) p.2)
        (encPair input encUnary) (encList encNat) := by
      apply ComputableInPolyTime.mapWithInput (encA := encUnary)
        (ComputableInPolyTime.range.comp (hsteps.comp hp))
      have hq := ComputableInPolyTime.fst (encPair input encUnary) encUnary
      have hk := ComputableInPolyTime.snd (encPair input encUnary) encUnary
      exact RotationCertificate.computableInPolyTime_walk.comp
        ((((hs.comp hp).comp hq).prod (ComputableInPolyTime.unary_succ.comp hk)).prod
          (hi.comp hq))
    have hfind := ComputableInPolyTime.findWithInput
      (test := fun (p : α × ℕ) j => decide (j < count p.1)) hwalks
      (ComputableInPolyTime.binary_lt'
        (ComputableInPolyTime.snd (encPair input encUnary) encNat)
        ((hbound.comp hp).comp (ComputableInPolyTime.fst (encPair input encUnary) encNat)))
    exact ComputableInPolyTime.optionGetDWithInput hfind (ComputableInPolyTime.const 0)
  exact encRotationCertificate_mk_deg.computableInPolyTime.comp hout

end Cslib.Complexity.CSP.OrderedBoundary
