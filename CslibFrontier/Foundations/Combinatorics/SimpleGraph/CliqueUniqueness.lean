/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card

/-!
# Uniqueness from outside degrees and small outside cliques

Suppose every vertex outside `S` has at most `5 |S| / 8` neighbors in `S`. A different
clique of size `|S|` must then have at least `3 |S| / 8` vertices outside `S`. Consequently,
excluding an outside clique of any size `r` with `8 r ≤ 3 |S|` ensures uniqueness.

This deterministic criterion lets a recovery algorithm accept the first verified clique,
even if it tries seeds that do not lie in the planted set before a successful planted seed.
-/

public section

namespace SimpleGraph

variable {V : Type*}
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A size-`|S|` clique equals `S` if outside degrees are at most `5 |S| / 8` and the
complement of `S` contains no clique of size `r ≤ 3 |S| / 8`. -/
theorem clique_eq_of_outside_degree_le_of_no_outside_clique
    {S Q : Finset V} {r : ℕ}
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card)
    (hr : 8 * r ≤ 3 * S.card)
    (hno : ∀ T : Finset V, Disjoint S T → T.card = r → ¬G.IsClique (T : Set V))
    (hQ : G.IsClique (Q : Set V)) (hcard : Q.card = S.card) : Q = S := by
  classical
  by_contra hne
  have hnot : ¬Q ⊆ S := by
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.ge)
  obtain ⟨v, hvQ, hvS⟩ := Finset.not_subset.mp hnot
  have hsub : Q ∩ S ⊆ S.filter (G.Adj v) := by
    intro w hw
    obtain ⟨hwQ, hwS⟩ := Finset.mem_inter.mp hw
    refine Finset.mem_filter.mpr ⟨hwS, hQ hvQ hwQ ?_⟩
    exact fun hvw => hvS (hvw.symm ▸ hwS)
  have hdeg := hdegree v hvS
  have hinter := Finset.card_le_card hsub
  have hsplit := Finset.card_sdiff_add_card_inter Q S
  have hout : r ≤ (Q \ S).card := by omega
  obtain ⟨T, hT, hTr⟩ := Finset.exists_subset_card_eq hout
  have hdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro w hwS hwT
    exact (Finset.mem_sdiff.mp (hT hwT)).2 hwS
  apply hno T hdisj hTr
  intro v hv w hw hvw
  exact hQ (Finset.mem_sdiff.mp (hT hv)).1 (Finset.mem_sdiff.mp (hT hw)).1 hvw

end SimpleGraph
