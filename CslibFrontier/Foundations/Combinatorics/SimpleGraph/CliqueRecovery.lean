/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
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
`S`, the missing vertices reduce each inside degree by at most their count plus one and
increase each outside degree by at most their count. The recovery theorem states exactly
the two inequalities needed to separate these degrees.

The recovery theorem is a deterministic step used by the planted-clique algorithm; its degree
and overlap assumptions are explicit.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep the vertices having at least three quarters of `k` neighbors in `T`. -/
@[expose] def recoverCliqueByDegree (k : ℕ) (T : Finset V) : Finset V :=
  Finset.univ.filter fun v => 3 * k ≤ 4 * (T.filter (G.Adj v)).card

/-- Degree cleanup recovers a clique when the candidate misses few enough vertices to keep
every inside degree above the threshold and every outside degree strictly below it. The
extra one in the inside inequality accounts for the missing self-loop. -/
theorem recoverCliqueByDegree_eq_of_overlap {S T : Finset V} {k : ℕ}
    (hS : S.card = k) (hT : T.card = k) (hclique : G.IsClique (S : Set V))
    (hmiss : 4 * ((S \ T).card + 1) ≤ k)
    (hout : ∀ v ∉ S, 4 * ((S.filter (G.Adj v)).card + (S \ T).card) < 3 * k) :
    G.recoverCliqueByDegree k T = S := by
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
