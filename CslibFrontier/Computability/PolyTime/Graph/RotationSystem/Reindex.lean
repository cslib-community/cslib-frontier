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
  unfold reindex
  apply encRotationCertificate_mk_polyTime
  apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
  have hback : ComputableInPolyTime (fun p : α × ℕ => back p.1 p.2)
      (encPair input encUnary) encNat :=
    hb.comp ((ComputableInPolyTime.fst input encUnary).prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd input encUnary)))
  have hread : ComputableInPolyTime
      (fun p : α × ℕ => (table p.1).successor.getD (back p.1 p.2) 0)
      (encPair input encUnary) encNat := by fun_prop
  exact hf.comp ((ComputableInPolyTime.fst input encUnary).prod hread)

/-- Exchange two computed binary-indexed outgoing entries. Even invalid corner indices
are only compared and read; the actual table length funds the iteration. -/
theorem computableInPolyTime_swapSuccessors {α : Type} {input : α ↪ List Bool}
    {table : α → RotationCertificate} {left right : α → ℕ}
    (hc : ComputableInPolyTime table input encRotationCertificate)
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun x => (table x).swapSuccessors (left x) (right x))
      input encRotationCertificate := by
  have hl' := hl.comp (ComputableInPolyTime.fst input encNat)
  have hr' := hr.comp (ComputableInPolyTime.fst input encNat)
  simpa only [swapSuccessors, reindex] using computableInPolyTime_reindex
    (forward := fun _ i => i)
    (back := fun x i => if i = left x then right x else if i = right x then left x else i)
    hc (by fun_prop) (ComputableInPolyTime.snd input encNat) (by fun_prop)

end Cslib.Complexity.Graph.RotationCertificate
