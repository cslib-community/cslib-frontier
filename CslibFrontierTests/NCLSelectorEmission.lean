/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.PolyTime

/-! Structural encoding words and a standard-encoding consumer of exact graph emission. -/

open Cslib.Complexity Cslib.Complexity.NCL Turing.MultiTapeTM
open SelectorNetwork.AndOr

example (r : WireRef) : encWireRef r = encPair encBool encUnary (r.boundary, r.index) := rfl

example (C : TemplateContext) : encTemplateContext C =
    encPair (encList encUnary) (encPair encUnary (encPair encBool encUnary))
      (C.boundaryNames, C.privateBase, C.reverse, C.anchor) := rfl

example {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q) :
    ComputableInPolyTime (fun n => AndOrGraph.ofFinite (HWord.Planarized.finiteGraph (n := n) H hq))
      encUnary encAndOrGraph := by
  have h := (Program.computableInPolyTime_graph (3 * q)).comp
    (HWord.Metadata.computableInPolyTime_blocks H hq)
  simpa only [Function.comp_def, HWord.Metadata.graph_blocks_eq] using h
