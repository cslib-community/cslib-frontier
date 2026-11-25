/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Communication.Announce
import CslibFrontier.Computability.Communication.Operations
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.IndepNum

/-!
# Clique versus independent set: Yannakakis' `O(log² n)` protocol

Fix a graph `G` on `n` vertices. Alice holds a clique `C` of `G`, Bob holds an independent set `I`,
and they must determine `|C ∩ I|`. This number is `0` or `1`, since two common vertices would be
both adjacent and non-adjacent. This module proves that `O(log² n)` bits suffice, uniformly in
`G` ([AroraBarak07], Chapter 12, Exercise 8).

The players keep a set `W` of vertices that contains `C ∩ I`. In each phase, Alice names a vertex
`v ∈ C ∩ W` with at most `|W| / 2` neighbours in `W`, if there is one, and Bob says whether
`v ∈ I`. If not, every common vertex lies in the clique `C` and differs from `v`, so it is a
neighbour of `v`, and `W` shrinks to the neighbours of `v` in `W`. If Alice has no eligible vertex,
Bob announces a vertex `u ∈ I ∩ W` with at most `|W| / 2` non-neighbours in `W \ {u}`, if there is
one, and Alice says whether `u ∈ C`. If not, every common vertex is a non-neighbour of `u`. If
neither player can announce a vertex, then `C ∩ I ∩ W` is empty: the neighbours and the
non-neighbours of a common vertex `w` in `W` are disjoint subsets of `W`, so one of the two counts
is at most `|W| / 2` and `w` would have been eligible. Each phase halves `W`, so `⌊log₂ n⌋ + 1`
phases of `2 ⌈log₂ (n + 1)⌉ + 1` bits suffice.

## Main results

* `Cslib.Communication.ecomplexity_clique_indepSet_le`: the communication complexity of
  computing `|C ∩ I|` on cliques × independent sets is at most `3 (⌊log₂ n⌋ + 1)²`.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Chapter 12, Exercise 8 (printed p. 232 / PDF p. 248).
-/

public section

namespace Cslib.Communication

open Finset

variable {V : Type*} {G : SimpleGraph V}

/-- `r` phases of the halving protocol, each of `2 ⌈log₂ (n + 1)⌉ + 1` bits, compute `|C ∩ I|`
when `C ∩ I` lies in a known set `W` of fewer than `2 ^ r` vertices. -/
private theorem exists_protocol_clique_indepSet [Fintype V] [DecidableEq V] (r : ℕ)
    (W : Finset V) :
    ∃ q : Protocol (Finset V) (Finset V) ℕ,
      q.depth ≤ r * (2 * Nat.clog 2 (Fintype.card V + 1) + 1) ∧
      (#W < 2 ^ r → ∀ C I : Finset V, G.IsClique (C : Set V) → G.IsIndepSet (I : Set V) →
        C ∩ I ⊆ W → q.run C I = #(C ∩ I)) := by
  classical
  induction r generalizing W with
  | zero =>
    refine ⟨.output 0, by simp, fun hW C I _ _ hsub => ?_⟩
    have hW : W = ∅ := card_eq_zero.mp (by simpa using hW)
    rw [Protocol.run_output, eq_comm, card_eq_zero, ← subset_empty, ← hW]
    exact hsub
  | succ r ih =>
    choose! next hnext hnext_run using ih
    -- The neighbours and the non-neighbours of a vertex inside `W`.
    let nbr (v : V) : Finset V := W.filter (G.Adj v)
    let nonNbr (u : V) : Finset V := W.filter fun w => w ≠ u ∧ ¬G.Adj u w
    let goodA (C : Finset V) (v : V) : Prop := v ∈ C ∧ v ∈ W ∧ 2 * #(nbr v) ≤ #W
    let goodB (I : Finset V) (u : V) : Prop := u ∈ I ∧ u ∈ W ∧ 2 * #(nonNbr u) ≤ #W
    let choiceA (C : Finset V) : Option V := if h : ∃ v, goodA C v then some h.choose else none
    let choiceB (I : Finset V) : Option V := if h : ∃ u, goodB I u then some h.choose else none
    obtain ⟨qa, hqa, hqa_run⟩ := Protocol.exists_run_eq_left (Y := Finset V) choiceA
    obtain ⟨qb, hqb, hqb_run⟩ := Protocol.exists_run_eq_right (X := Finset V) choiceB
    rw [Fintype.card_option] at hqa hqb
    let afterB : Option V → Protocol (Finset V) (Finset V) ℕ
      | some u => .alice (fun C => decide (u ∈ C)) (next (nonNbr u)) (.output 1)
      | none => .output 0
    let afterA : Option V → Protocol (Finset V) (Finset V) ℕ
      | some v => .bob (fun I => decide (v ∈ I)) (next (nbr v)) (.output 1)
      | none => qb.bind afterB
    refine ⟨qa.bind afterA, ?_, fun hW C I hC hI hsub => ?_⟩
    · set c := Nat.clog 2 (Fintype.card V + 1)
      have hB : ∀ o, (afterB o).depth ≤ 1 + r * (2 * c + 1) := by
        rintro (_ | u)
        · simp [afterB]
        · simp only [afterB, Protocol.depth_alice, Protocol.depth_output]
          have := hnext (nonNbr u)
          omega
      have hA : ∀ o, (afterA o).depth ≤ c + 1 + r * (2 * c + 1) := by
        rintro (_ | v)
        · exact (Protocol.depth_bind_le hB).trans (by omega)
        · simp only [afterA, Protocol.depth_bob, Protocol.depth_output]
          have := hnext (nbr v)
          omega
      have hmul : (r + 1) * (2 * c + 1) = r * (2 * c + 1) + (2 * c + 1) := by ring
      refine (Protocol.depth_bind_le hA).trans ?_
      omega
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
    -- A named vertex in both sets is their unique common vertex.
    have hone : ∀ v ∈ C, v ∈ I → 1 = #(C ∩ I) := fun v hvC hvI =>
      le_antisymm (card_pos.mpr ⟨v, mem_inter.mpr ⟨hvC, hvI⟩⟩)
        (G.card_inter_le_one_of_isClique_of_isIndepSet hC hI)
    rw [Protocol.run_bind, hqa_run]
    by_cases hA : ∃ v, goodA C v
    · obtain ⟨hvC, -, hv⟩ := hA.choose_spec
      simp only [choiceA, dite_eq_left hA, afterA, Protocol.run_bob]
      set v := hA.choose
      by_cases hvI : v ∈ I
      · simpa [hvI] using hone v hvC hvI
      simp only [hvI, decide_false, Bool.cond_false]
      refine hnext_run _ (by omega) C I hC hI fun w hw => ?_
      obtain ⟨hwC, hwI⟩ := mem_inter.mp hw
      exact mem_filter.mpr ⟨hsub hw, hC hvC hwC fun h => hvI (h ▸ hwI)⟩
    by_cases hB : ∃ u, goodB I u
    · obtain ⟨huI, -, hu⟩ := hB.choose_spec
      simp only [choiceA, dite_eq_right hA, afterA, Protocol.run_bind, hqb_run, choiceB,
        dite_eq_left hB, afterB, Protocol.run_alice]
      set u := hB.choose
      by_cases huC : u ∈ C
      · simpa [huC] using hone u huC huI
      simp only [huC, decide_false, Bool.cond_false]
      refine hnext_run _ (by omega) C I hC hI fun w hw => ?_
      obtain ⟨hwC, hwI⟩ := mem_inter.mp hw
      have hne : w ≠ u := fun h => huC (h ▸ hwC)
      exact mem_filter.mpr ⟨hsub hw, hne, hI huI hwI hne.symm⟩
    -- Neither player can announce a vertex: no vertex is common.
    simp only [choiceA, dite_eq_right hA, afterA, Protocol.run_bind, hqb_run, choiceB,
      dite_eq_right hB, afterB, Protocol.run_output]
    refine (card_eq_zero.mpr (eq_empty_of_forall_notMem fun w hw => ?_)).symm
    obtain ⟨hwC, hwI⟩ := mem_inter.mp hw
    have hA' : ¬ 2 * #(nbr w) ≤ #W := fun h => hA ⟨w, hwC, hsub hw, h⟩
    have hB' : ¬ 2 * #(nonNbr w) ≤ #W := fun h => hB ⟨w, hwI, hsub hw, h⟩
    have hdisj : Disjoint (nbr w) (nonNbr w) :=
      disjoint_filter.mpr fun _ _ hadj hnon => hnon.2 hadj
    have := (card_union_of_disjoint hdisj).symm.trans_le (card_le_card
      (union_subset (filter_subset _ W) (filter_subset _ W) : nbr w ∪ nonNbr w ⊆ W))
    omega

/-- **Clique versus independent set** (Yannakakis; [AroraBarak07], Chapter 12, Exercise 8):
for every graph `G` on `n` vertices, if Alice holds a clique `C` and Bob an independent set `I`,
they can determine `|C ∩ I|` with at most `3 (⌊log₂ n⌋ + 1)²` bits. This is `O(log² n)`,
uniformly in `G`. The communication complexity is that of the relation "output `|C ∩ I|`" on
cliques × independent sets, with deterministic protocol trees whose output both players know. -/
theorem ecomplexity_clique_indepSet_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    Protocol.ecomplexity (fun C I z => z = #(C ∩ I))
        {C : Finset V | G.IsClique (C : Set V)} {I : Finset V | G.IsIndepSet (I : Set V)} ≤
      (3 * (Nat.log 2 (Fintype.card V) + 1) ^ 2 : ℕ) := by
  set n := Fintype.card V
  obtain ⟨q, hq, hrun⟩ :=
    exists_protocol_clique_indepSet (G := G) (Nat.log 2 n + 1) (univ : Finset V)
  refine Protocol.ecomplexity_le_iff.mpr
    ⟨q, fun C hC I hI => hrun (by simpa using Nat.lt_pow_succ_log_self one_lt_two n) C I hC hI
      (subset_univ _), hq.trans ?_⟩
  have hc : Nat.clog 2 (n + 1) ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self one_lt_two n)
  calc (Nat.log 2 n + 1) * (2 * Nat.clog 2 (n + 1) + 1)
      ≤ (Nat.log 2 n + 1) * (3 * (Nat.log 2 n + 1)) := by gcongr; omega
    _ = 3 * (Nat.log 2 n + 1) ^ 2 := by ring

end Cslib.Communication
