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
# Recovering a clique from an approximate vertex set

`SimpleGraph.recoverCliqueByDegree G k T` retains the vertices with at least `3 k / 4`
neighbors in `T`, expressed without truncated division. If `T` has the same size as a clique
`S`, misses at most a sixteenth of `S`, and vertices outside `S` have at most `5 k / 8`
neighbors in `S`, this operation recovers `S` exactly.

The recovery theorem is a deterministic step used by the planted-clique algorithm; its degree
and overlap assumptions are explicit. The constants are chosen for a simple rounding argument.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep the vertices having at least three quarters of `k` neighbors in `T`. -/
@[expose] def recoverCliqueByDegree (k : ℕ) (T : Finset V) : Finset V :=
  Finset.univ.filter fun v => 3 * k ≤ 4 * (T.filter (G.Adj v)).card

/-- The deterministic cleanup step of clique recovery. A candidate set of size `k` missing at
most `k / 16` clique vertices is corrected by the degree threshold, provided every outside
vertex has at most `5 k / 8` neighbors in the clique. -/
theorem recoverCliqueByDegree_eq_of_overlap {S T : Finset V} {k : ℕ}
    (hS : S.card = k) (hT : T.card = k) (hclique : G.IsClique (S : Set V))
    (hmiss : 16 * (S \ T).card ≤ k)
    (hout : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * k)
    (hk : 6 ≤ k) : G.recoverCliqueByDegree k T = S := by
  have hdiff : (S \ T).card = (T \ S).card :=
    Finset.card_sdiff_comm (hS.trans hT.symm)
  ext v
  simp only [recoverCliqueByDegree, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    by_contra hvS
    have hsub : T.filter (G.Adj v) ⊆ S.filter (G.Adj v) ∪ (T \ S) := by
      intro w hw
      obtain ⟨hwT, hvw⟩ := Finset.mem_filter.mp hw
      by_cases hwS : w ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwS, hvw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwT, hwS⟩)
    have hdegree := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have ho := hout v hvS
    omega
  · intro hvS
    have hsub : (S ∩ T).erase v ⊆ T.filter (G.Adj v) := by
      intro w hw
      obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
      obtain ⟨hwS, hwT⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_filter.mpr ⟨hwT, hclique hvS hwS hwv.symm⟩
    have hdegree := Finset.card_le_card hsub
    have herase := Finset.pred_card_le_card_erase (a := v) (s := S ∩ T)
    have hsplit := Finset.card_inter_add_card_sdiff S T
    omega

end SimpleGraph
