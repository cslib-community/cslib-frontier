/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Network.Contagion

/-!
# Collected results: networked coordination games and Morris's contagion threshold
-/

register_result "morris-progressive-nonprogressive-contagion" where
  title := "Equivalence of progressive and nonprogressive finite contagious sets"
  topic := "game theory"
  sources := [
    { paper := Kleinberg2007, theorem := "Theorem 24.1", locator := "Section 24.2, p. 617" },
    { paper := Morris2000, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Network.exists_finset_isContagious_bestResponseStep_iff_progressiveStep
  ]
  scope := "Locally finite undirected simple graphs G : SimpleGraph V and real thresholds q ≤ 1 \
    (covering Kleinberg's standing assumptions of countably infinite locally finite graphs and \
    0 < q < 1). Uses the cross-multiplied best-response step h_q(S) = {v | q * d_v ≤ |N(v) ∩ S|} \
    (ties broken in favor of B) and progressive step h̄_q(S) = S ∪ h_q(S), with IsContagious \
    requiring eventual permanent conversion of every vertex (∀ w, ∃ k, ∀ j ≥ k, w ∈ step^[j] S). \
    Discarding isolated vertices from h̄_q^ℓ(S) yields a finite nonprogressive witness without \
    excluding isolated vertices."

register_result "morris-contagion-threshold-le-half" where
  title := "Morris's 1/2 upper bound on the contagion threshold of infinite graphs"
  topic := "game theory"
  sources := [
    { paper := Kleinberg2007, theorem := "Theorem 24.2", locator := "Section 24.2, p. 618" },
    { paper := Morris2000, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Network.not_isContagious_progressiveStep_of_half_lt,
    Cslib.GameTheory.Network.not_isContagious_bestResponseStep_of_half_lt,
    Cslib.GameTheory.Network.contagionThreshold_le_half
  ]
  scope := "Infinite locally finite simple graphs G : SimpleGraph V with no isolated vertices \
    (∀ v, 0 < G.degree v; implied by G.Connected on any infinite vertex type). Positive degree \
    makes the neighbor fraction d_v^B / d_v well-defined and rules out isolated vertices \
    trivially adopting B under the tie-breaking rule 0 ≥ q * 0 (on ⊥ : SimpleGraph ℕ, ∅ is \
    contagious for every q). The contagion threshold is formalized as sSup over q ∈ [0, 1] \
    admitting a finite contagious set, refining Kleinberg's informal maximum wording on p. 615 \
    to Morris's supremum; it coincides with sSup over (0, 1) on every locally finite graph."
