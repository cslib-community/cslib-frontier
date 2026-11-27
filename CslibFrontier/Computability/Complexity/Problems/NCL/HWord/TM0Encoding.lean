/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.TM0Equivalence
public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0WindowEncoding
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Problem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Standard encodings of finite-window configurations and tape words

A configuration uses the standard structural encoding of its control, scanned symbol, and
two lists. Its configuration word is built by finite letter maps, reversal and concatenation.

## Main results

* `TM0Window.computableInPolyTime_numberedWord`: fixed finite numbering of the same word.
-/

public section

noncomputable section

namespace Cslib.Complexity.NCL.TM0Window
open Turing.TM0Window Turing.MultiTapeTM Cslib.PostCorrespondence.OfTM0.Letter
variable {Γ Q : Type} [Finite Γ] [Finite Q]

/-- The framed stable tape word is produced in polynomial time from its four fields. -/
@[fun_prop]
private theorem computableInPolyTime_stableWord :
    ComputableInPolyTime (fun c : Cfg Γ Q => Rules.word (.stable c)) (encCfg (Γ := Γ) (Q := Q))
      (encList (encFinite (Symbol Γ Q))) := by
  have hL : ComputableInPolyTime
      (fun c : Cfg Γ Q => c.left.reverse.map fun a => (sym (a, false) : Symbol Γ Q))
      (encCfg (Γ := Γ) (Q := Q)) (encList (encFinite (Symbol Γ Q))) :=
    (ComputableInPolyTime.of_finite _).map.comp
      ((ComputableInPolyTime.listReverse _).comp (by fun_prop))
  have hR : ComputableInPolyTime
      (fun c : Cfg Γ Q => c.right.map fun a => (sym (a, true) : Symbol Γ Q))
      (encCfg (Γ := Γ) (Q := Q)) (encList (encFinite (Symbol Γ Q))) :=
    (ComputableInPolyTime.of_finite _).map.comp (by fun_prop)
  have hp : ComputableInPolyTime (fun c : Cfg Γ Q => (c.state, c.scanned))
      (encCfg (Γ := Γ) (Q := Q)) (encPair (encFinite Q) (encFinite Γ)) := by fun_prop
  have hhead : ComputableInPolyTime
      (fun c : Cfg Γ Q => (cell (.running c.state) (c.scanned, false) : Symbol Γ Q))
      (encCfg (Γ := Γ) (Q := Q)) (encFinite (Symbol Γ Q)) :=
    (ComputableInPolyTime.of_finite
      (fun p : Q × Γ => (cell (.running p.1) (p.2, false) : Symbol Γ Q))).comp
      hp
  simpa only [Rules.word, Rules.frame, List.cons_append, List.nil_append,
    List.append_assoc] using
    (ComputableInPolyTime.const (lb : Symbol Γ Q)).cons'
      (hL.listAppend' (hhead.cons' (hR.listAppend' (ComputableInPolyTime.const [rb]))))

variable [Fintype (Symbol Γ Q)]

/-- Number the actual stable tape word in its fixed finite alphabet. -/
@[expose] noncomputable def numberedWord (c : Cfg Γ Q) :
    List (Fin (Fintype.card (Symbol Γ Q))) :=
  (Rules.word (.stable c)).map (Fintype.equivFin (Symbol Γ Q))

/-- Fixed finite letter numbering preserves the polynomial-time word algorithm. -/
@[fun_prop]
theorem computableInPolyTime_numberedWord :
    ComputableInPolyTime (numberedWord (Γ := Γ) (Q := Q)) (encCfg (Γ := Γ) (Q := Q))
      (HWord.encWord (Fintype.card (Symbol Γ Q))) :=
  (ComputableInPolyTime.of_finite _).map.comp computableInPolyTime_stableWord

end Cslib.Complexity.NCL.TM0Window

end
