/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Linear

register_result "khanna-putterman-song-linear-msf-comparisons" where
  title := "The deterministic comparison complexity of minimum spanning forests is linear"
  topic := "graph algorithms"
  sources := [
    { paper := KhannaPuttermanSong2026,
      theorem := "Theorem 4.1",
      locator := "§4, p. 25 (T* defined in §1.1, p. 5); final.pdf at commit 0072335" }
  ]
  theorems := [
    Cslib.Query.exists_msf_program_countQueries_le
  ]
  scope := "One absolute constant C : ℕ such that for every finite multigraph \
    ends : E → Sym2 V with edge set S : Finset E (parallel edges, self-loops and disconnected \
    graphs allowed) there is a comparison program p : FreeM (LEQuery E) (Finset E), chosen \
    before the weights, that for every injective w : E → W into a linear order (W : Type) \
    returns Cslib.Multigraph.msf ends w S against LEQuery.keyOracle w with at most C * #S \
    comparisons. This is T*(m, n) = O(m) for the decision-tree model of p. 5, over multigraphs, \
    which contain the paper's simple graphs; free computation between comparisons as in that \
    model. Distinct weights as in §2 (p. 11); no tie-breaking corollary is registered. The \
    running time of Theorem 1.1 / Corollary 4.2 is not proved: it rests on Pettie and \
    Ramachandran 2002, which is not formalized."
