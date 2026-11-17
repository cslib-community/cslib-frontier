/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateReindex
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCornerSwap
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native raw successor-table reindexing

Forward and inverse index maps operate on binary naturals, including arbitrarily large
malformed entries. The only enumeration uses a computed unary count, supplied from actual
graph or list lengths by callers. No abstract dart inverse executes at runtime.
Exchanging two outgoing table entries is a specialization of the same raw program.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

open Turing.MultiTapeTM

/-- Native reindexing composes the supplied binary programs around saturating binary
table lookup. The output clock is unary and independent of source entry magnitudes. -/
theorem computableInPolyTime_reindex {α : Type} {input : α ↪ List Bool}
    {table : α → RotationCertificate} {count : α → ℕ} {forward back : α → ℕ → ℕ}
    (hc : ComputableInPolyTime table input encRotationCertificate)
    (hn : ComputableInPolyTime count input encUnary)
    (hf : ComputableInPolyTime (fun p : α × ℕ => forward p.1 p.2)
      (encPair input encNat) encNat)
    (hb : ComputableInPolyTime (fun p : α × ℕ => back p.1 p.2)
      (encPair input encNat) encNat) :
    ComputableInPolyTime (fun x => reindex (table x) (count x) (forward x) (back x))
      input encRotationCertificate := by
  have hw : ComputableInPolyTime (fun x => (List.range (count x)).map
      (fun i => forward x ((table x).successor.getD (back x i) 0))) input (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput (encA := encUnary)
      (ComputableInPolyTime.range.comp hn)
    have hx := ComputableInPolyTime.fst input encUnary
    have hi := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd input encUnary)
    have hback := hb.comp (hx.prod hi)
    have htable := computableInPolyTime_successor.comp (hc.comp hx)
    have hread := ComputableInPolyTime.listGetD_binary (encA := encNat) 0 htable hback
    exact hf.comp (hx.prod hread)
  exact encRotationCertificate_mk_deg.computableInPolyTime.comp hw

/-- Exchange two computed binary-indexed outgoing entries. Even invalid corner indices
are only compared and read; the actual table length funds the iteration. -/
theorem computableInPolyTime_swapSuccessors {α : Type} {input : α ↪ List Bool}
    {table : α → RotationCertificate} {left right : α → ℕ}
    (hc : ComputableInPolyTime table input encRotationCertificate)
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => (table x).swapSuccessors (left x) (right x))
      input encRotationCertificate := by
  have hn : ComputableInPolyTime (fun x => (table x).successor.length) input encUnary := by
    have hs := computableInPolyTime_successor.comp hc
    exact (ComputableInPolyTime.length_list encNat).comp hs
  have hl' := hl.comp (ComputableInPolyTime.fst input encNat)
  have hr' := hr.comp (ComputableInPolyTime.fst input encNat)
  have hb : ComputableInPolyTime (fun p : α × ℕ =>
      if p.2 = left p.1 then right p.1 else if p.2 = right p.1 then left p.1 else p.2)
      (encPair input encNat) encNat := by fun_prop
  have h := computableInPolyTime_reindex
    (forward := fun _ i => i)
    (back := fun x i => if i = left x then right x else if i = right x then left x else i)
    hc hn (ComputableInPolyTime.snd input encNat) hb
  simpa only [swapSuccessors, reindex] using h

end Cslib.Complexity.Graph.RotationCertificate
