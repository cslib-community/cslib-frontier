/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Rectifier.Basic
public import CslibFrontier.Foundations.Combinatorics.BrownMatrix
import Mathlib.Data.Fintype.Sum
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relative `OR`-complexity of Boolean matrices and their complements

Igor S. Sergeev ([Sergeev2014ORComplement], pp. 1–3) constructs explicit `n × n` Boolean matrices
whose rectifier (`OR`) complexity is linear (`OR_3(C) = O(n)`), while their entrywise complements
`C̄` are `2`-rectangle-free with `OR(C̄) = |C̄| = Ω(n^{4/3})`.

Given an `m × m` Boolean matrix `A`, let `B = twoRectMatrix A` be its `n × n` `2`-rectangle lift
(`n = C(m, 2)`):

* **Depth-`3` upper bound for `B̄`** (`complTwoRectCircuit`,
  `orDepthComplexity_three_compl_twoRectMatrix_le`): a `4`-layer rectifier circuit connects input
  `c` to column `j ∈ c` (`2 n` edges), column `j` to row `i` whenever `A i j = false` (`|Ā|`
  edges), and row `i` to output `r` whenever `i ∈ r` (`2 n` edges), giving
  `OR_3(B̄) ≤ 4 n + |Ā| ≤ 7 n` (`3 ≤ m`).
* **General `k`-free separation (`Lemma 3`)**
  (`pow_four_boolMatrixWeight_le_eight_mul_orComplexity_twoRectMatrix`): if `A` is `k`-free and
  `4 * m ^ 3 ≤ |A| ^ 2`, combining Lemma 1, Lemma 2, and Nechiporuk's bound yields
  `|A| ^ 4 ≤ 8 * (k * m) ^ 4 * OR(B)` (note that [Sergeev2014ORComplement], Lemma 3, pp. 2–3
  writes `(|A| / (k n)) ^ 4` due to reusing Lemma 1's dimension variable `n` after setting
  `n = C(m, 2)` for an `m × m` matrix `A`; Lemma 1 on the `m × m` matrix `A` gives
  `|B| = Ω((|A| / m) ^ 4)` and `OR(B) = Ω((|A| / (k m)) ^ 4)`).
* **Explicit `O(n)` vs. `Ω(n^{4/3})` separation (`Theorem 1(ii)`)**
  (`sergeevComplementMatrix`, `orDepthComplexity_three_sergeevComplementMatrix_le`,
  `isRectangleFreeMatrix_compl_sergeevComplementMatrix`,
  `orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight`,
  `choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three`,
  `exists_gt_sergeev_or_complement_separation`): instantiating `A = brownMatrix p` (`m = p ^ 3`,
  `p` prime with `p ≡ 3 (mod 4)`) produces explicit `n × n` matrices `C = B̄` (`n = C(p ^ 3, 2)`)
  satisfying `OR(C) ≤ OR_3(C) ≤ 7 * n`, `C̄` is `2`-free, `OR(C̄) = |C̄|`, and
  `n ^ 4 ≤ 2 ^ 23 * OR(C̄) ^ 3` (for arbitrarily large `n` via Dirichlet's theorem). Theorem 1(i)'s
  projective norm-graph instantiation ([KollarRonyaiSzabo1996], with
  `Δ = 2^{O(√(log m log log m))}` giving `OR(C̄) / OR(C) = n · 2^{-O(√(ln n ln ln n))}`) remains
  open under [#7622](https://github.com/cslib-community/cslib-frontier/issues/7622), with Lemma 3
  supplying its general reduction step.

## Main definitions

* `Cslib.Circuits.ComplTwoRectVertex`: the four vertex layers of Sergeev's depth-`3` circuit.
* `Cslib.Circuits.complTwoRectCircuit`: Sergeev's explicit depth-`3` rectifier circuit for
  `(twoRectMatrix A).map (! ·)`.
* `Cslib.Circuits.sergeevComplementMatrix`: the explicit `C(p ^ 3, 2) × C(p ^ 3, 2)` matrix
  `(twoRectMatrix (brownMatrix p)).map (! ·)`.

## Main results

* `Cslib.Circuits.size_complTwoRectCircuit`, `Cslib.Circuits.hasDepthLE_three_complTwoRectCircuit`,
  `Cslib.Circuits.computes_complTwoRectCircuit`: size, depth `3`, and correctness of
  `complTwoRectCircuit`.
* `Cslib.Circuits.orDepthComplexity_three_compl_twoRectMatrix_le`,
  `Cslib.Circuits.orDepthComplexity_three_compl_twoRectMatrix_le_seven_mul`: Sergeev's Lemma 3
  upper bounds `OR_3(B̄) ≤ 4 n + |Ā| ≤ 7 n`.
* `Cslib.Circuits.pow_four_boolMatrixWeight_le_eight_mul_orComplexity_twoRectMatrix`: Sergeev's
  Lemma 3 lower bound `|A| ^ 4 ≤ 8 * (k * m) ^ 4 * OR(twoRectMatrix A)`.
* `Cslib.Circuits.orDepthComplexity_three_sergeevComplementMatrix_le`,
  `Cslib.Circuits.orComplexity_sergeevComplementMatrix_le`,
  `Cslib.Circuits.isRectangleFreeMatrix_compl_sergeevComplementMatrix`,
  `Cslib.Circuits.orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight`,
  `Cslib.Circuits.choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three`,
  `Cslib.Circuits.exists_gt_sergeev_or_complement_separation`: Sergeev's Theorem 1(ii).

## References

* [I. S. Sergeev, *On relative OR-complexity of Boolean matrices and their
  complements*][Sergeev2014ORComplement], Theorem 1(ii) and Lemma 3, pp. 1–3
* [W. G. Brown, *On graphs that do not contain a Thomsen graph*][Brown1966]
-/

public section

namespace Cslib.Circuits

open Finset Function

variable {α β : Type*}

/-- Vertex layers of Sergeev's depth-`3` rectifier circuit implementing
`(twoRectMatrix A).map (! ·)` ([Sergeev2014ORComplement], p. 3). -/
inductive ComplTwoRectVertex (α β : Type*) where
  /-- Layer `0`: input pole for a `2`-element column subset `c`. -/
  | inp (c : {c : Finset β // #c = 2})
  /-- Layer `1`: column vertex `j : β`. -/
  | col (j : β)
  /-- Layer `2`: row vertex `i : α`. -/
  | row (i : α)
  /-- Layer `3`: output pole for a `2`-element row subset `r`. -/
  | out (r : {r : Finset α // #r = 2})
  deriving DecidableEq

private def complTwoRectVertexEquiv (α β : Type*) :
    ComplTwoRectVertex α β ≃
      ({c : Finset β // #c = 2} ⊕ β) ⊕ (α ⊕ {r : Finset α // #r = 2}) where
  toFun
    | .inp c => .inl (.inl c)
    | .col j => .inl (.inr j)
    | .row i => .inr (.inl i)
    | .out r => .inr (.inr r)
  invFun
    | .inl (.inl c) => .inp c
    | .inl (.inr j) => .col j
    | .inr (.inl i) => .row i
    | .inr (.inr r) => .out r
  left_inv v := by cases v <;> rfl
  right_inv s := by rcases s with (c | j) | (i | r) <;> rfl

instance [Finite α] [Finite β] : Finite (ComplTwoRectVertex α β) := by
  cases nonempty_fintype α
  cases nonempty_fintype β
  exact Finite.of_equiv _ (complTwoRectVertexEquiv α β).symm

private def inpEdges [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (ComplTwoRectVertex α β × ComplTwoRectVertex α β) :=
  (univ : Finset {c : Finset β // #c = 2}).biUnion fun c =>
    c.val.map ⟨fun j => (.inp c, .col j), fun _ _ h =>
      ComplTwoRectVertex.col.inj (Prod.mk.inj h).2⟩

private def midEdges [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    Finset (ComplTwoRectVertex α β × ComplTwoRectVertex α β) :=
  ((univ : Finset (α × β)).filter fun p => A p.1 p.2 = false).map
    ⟨fun p => (.col p.2, .row p.1), fun _ _ h =>
      Prod.ext (ComplTwoRectVertex.row.inj (Prod.mk.inj h).2)
        (ComplTwoRectVertex.col.inj (Prod.mk.inj h).1)⟩

private def outEdges [Fintype α] [DecidableEq α] [DecidableEq β] :
    Finset (ComplTwoRectVertex α β × ComplTwoRectVertex α β) :=
  (univ : Finset {r : Finset α // #r = 2}).biUnion fun r =>
    r.val.map ⟨fun i => (.row i, .out r), fun _ _ h =>
      ComplTwoRectVertex.row.inj (Prod.mk.inj h).1⟩

private theorem card_inpEdges [Fintype β] [DecidableEq α] [DecidableEq β] :
    #(inpEdges (α := α) (β := β)) = 2 * (Fintype.card β).choose 2 := by
  rw [inpEdges, card_biUnion]
  · calc ∑ c : {c : Finset β // #c = 2}, #(c.val.map _)
        = ∑ c : {c : Finset β // #c = 2}, #c.val := sum_congr rfl fun c _ => card_map _
      _ = ∑ c : {c : Finset β // #c = 2}, 2 := sum_congr rfl fun c _ => c.property
      _ = 2 * (Fintype.card β).choose 2 := by
          rw [sum_const, card_univ, card_twoSubsets, smul_eq_mul, mul_comm]
  · intro c₁ _ c₂ _ hne
    refine disjoint_left.mpr fun e he₁ he₂ => hne ?_
    obtain ⟨_, -, rfl⟩ := mem_map.mp he₁
    obtain ⟨_, -, heq⟩ := mem_map.mp he₂
    exact ComplTwoRectVertex.inp.inj (Prod.mk.inj heq).1.symm

private theorem card_midEdges [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    #(midEdges A) = boolMatrixWeight (A.map (! ·)) := by
  rw [midEdges, card_map, boolMatrixWeight]
  congr 2
  ext p
  simp only [Matrix.map_apply, Bool.not_eq_true']

private theorem card_outEdges [Fintype α] [DecidableEq α] [DecidableEq β] :
    #(outEdges (α := α) (β := β)) = 2 * (Fintype.card α).choose 2 := by
  rw [outEdges, card_biUnion]
  · calc ∑ r : {r : Finset α // #r = 2}, #(r.val.map _)
        = ∑ r : {r : Finset α // #r = 2}, #r.val := sum_congr rfl fun r _ => card_map _
      _ = ∑ r : {r : Finset α // #r = 2}, 2 := sum_congr rfl fun r _ => r.property
      _ = 2 * (Fintype.card α).choose 2 := by
          rw [sum_const, card_univ, card_twoSubsets, smul_eq_mul, mul_comm]
  · intro r₁ _ r₂ _ hne
    refine disjoint_left.mpr fun e he₁ he₂ => hne ?_
    obtain ⟨_, -, rfl⟩ := mem_map.mp he₁
    obtain ⟨_, -, heq⟩ := mem_map.mp he₂
    exact ComplTwoRectVertex.out.inj (Prod.mk.inj heq).2.symm

section ComplTwoRectCircuit

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Sergeev's depth-`3` rectifier circuit** implementing `(twoRectMatrix A).map (! ·)`
([Sergeev2014ORComplement], p. 3). -/
def complTwoRectCircuit (A : Matrix α β Bool) :
    RectifierCircuit {r : Finset α // #r = 2} {c : Finset β // #c = 2}
      (ComplTwoRectVertex α β) where
  edges := inpEdges ∪ midEdges A ∪ outEdges
  inp := ⟨ComplTwoRectVertex.inp, fun _ _ h => ComplTwoRectVertex.inp.inj h⟩
  out := ⟨ComplTwoRectVertex.out, fun _ _ h => ComplTwoRectVertex.out.inj h⟩
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨c, rfl⟩ _ ⟨r, rfl⟩ h
    nomatch h

/-- Exact edge count of `complTwoRectCircuit A`. -/
theorem size_complTwoRectCircuit (A : Matrix α β Bool) :
    (complTwoRectCircuit A).size =
      2 * (Fintype.card β).choose 2 + boolMatrixWeight (A.map (! ·)) +
        2 * (Fintype.card α).choose 2 := by
  have hd12 : Disjoint (inpEdges (α := α) (β := β)) (midEdges A) := by
    refine disjoint_left.mpr fun e he₁ he₂ => ?_
    obtain ⟨c, -, hj⟩ := mem_biUnion.mp he₁
    obtain ⟨j, -, rfl⟩ := mem_map.mp hj
    obtain ⟨p, -, heq⟩ := mem_map.mp he₂
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  have hd123 : Disjoint (inpEdges (α := α) (β := β) ∪ midEdges A) outEdges := by
    refine disjoint_left.mpr fun e he₁₂ he₃ => ?_
    obtain ⟨r, -, hi⟩ := mem_biUnion.mp he₃
    obtain ⟨i, -, rfl⟩ := mem_map.mp hi
    rcases mem_union.mp he₁₂ with he₁ | he₂
    · obtain ⟨c, -, hj⟩ := mem_biUnion.mp he₁
      obtain ⟨j, -, heq⟩ := mem_map.mp hj
      have hbad := (Prod.mk.inj heq).1
      nomatch hbad
    · obtain ⟨p, -, heq⟩ := mem_map.mp he₂
      have hbad := (Prod.mk.inj heq).1
      nomatch hbad
  rw [RectifierCircuit.size, complTwoRectCircuit, card_union_of_disjoint hd123,
    card_union_of_disjoint hd12, card_inpEdges, card_midEdges, card_outEdges]

private def complLayer : ComplTwoRectVertex α β → ℕ
  | .inp _ => 0
  | .col _ => 1
  | .row _ => 2
  | .out _ => 3

/-- `complTwoRectCircuit A` has depth at most `3`. -/
theorem hasDepthLE_three_complTwoRectCircuit (A : Matrix α β Bool) :
    (complTwoRectCircuit A).HasDepthLE 3 := by
  refine RectifierCircuit.hasDepthLE_of_layer complLayer ?_ ?_
  · rintro u v huv
    simp only [complTwoRectCircuit, mem_union] at huv
    rcases huv with (h₁ | h₂) | h₃
    · obtain ⟨c, -, hj⟩ := mem_biUnion.mp h₁
      obtain ⟨j, -, heq⟩ := mem_map.mp hj
      change (ComplTwoRectVertex.inp c, ComplTwoRectVertex.col j) = (u, v) at heq
      rw [← (Prod.mk.inj heq).1, ← (Prod.mk.inj heq).2]
      rfl
    · obtain ⟨p, -, heq⟩ := mem_map.mp h₂
      change (ComplTwoRectVertex.col p.2, ComplTwoRectVertex.row p.1) = (u, v) at heq
      rw [← (Prod.mk.inj heq).1, ← (Prod.mk.inj heq).2]
      rfl
    · obtain ⟨r, -, hi⟩ := mem_biUnion.mp h₃
      obtain ⟨i, -, heq⟩ := mem_map.mp hi
      change (ComplTwoRectVertex.row i, ComplTwoRectVertex.out r) = (u, v) at heq
      rw [← (Prod.mk.inj heq).1, ← (Prod.mk.inj heq).2]
      rfl
  · rintro (_ | _ | _ | _) <;> simp only [complLayer] <;> decide

private theorem step_from_inp {A : Matrix α β Bool} {c : {c : Finset β // #c = 2}}
    {v : ComplTwoRectVertex α β} (h : (.inp c, v) ∈ (complTwoRectCircuit A).edges) :
    ∃ j ∈ c.val, v = .col j := by
  simp only [complTwoRectCircuit, mem_union] at h
  rcases h with (h₁ | h₂) | h₃
  · obtain ⟨c', -, hj⟩ := mem_biUnion.mp h₁
    obtain ⟨j, hjc', heq⟩ := mem_map.mp hj
    change (ComplTwoRectVertex.inp c', ComplTwoRectVertex.col j) = (.inp c, v) at heq
    have hc : c' = c := ComplTwoRectVertex.inp.inj (Prod.mk.inj heq).1
    subst hc
    exact ⟨j, hjc', (Prod.mk.inj heq).2.symm⟩
  · obtain ⟨p, -, heq⟩ := mem_map.mp h₂
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨r, -, hi⟩ := mem_biUnion.mp h₃
    obtain ⟨i, -, heq⟩ := mem_map.mp hi
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad

private theorem step_from_col {A : Matrix α β Bool} {j : β} {v : ComplTwoRectVertex α β}
    (h : (.col j, v) ∈ (complTwoRectCircuit A).edges) :
    ∃ i : α, A i j = false ∧ v = .row i := by
  simp only [complTwoRectCircuit, mem_union] at h
  rcases h with (h₁ | h₂) | h₃
  · obtain ⟨c, -, hj⟩ := mem_biUnion.mp h₁
    obtain ⟨j', -, heq⟩ := mem_map.mp hj
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨⟨i, j'⟩, hmem, heq⟩ := mem_map.mp h₂
    change (ComplTwoRectVertex.col j', ComplTwoRectVertex.row i) = (.col j, v) at heq
    have hj_eq : j' = j := ComplTwoRectVertex.col.inj (Prod.mk.inj heq).1
    subst hj_eq
    exact ⟨i, (mem_filter.mp hmem).2, (Prod.mk.inj heq).2.symm⟩
  · obtain ⟨r, -, hi⟩ := mem_biUnion.mp h₃
    obtain ⟨i, -, heq⟩ := mem_map.mp hi
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad

private theorem step_from_row {A : Matrix α β Bool} {i : α} {v : ComplTwoRectVertex α β}
    (h : (.row i, v) ∈ (complTwoRectCircuit A).edges) :
    ∃ r : {r : Finset α // #r = 2}, i ∈ r.val ∧ v = .out r := by
  simp only [complTwoRectCircuit, mem_union] at h
  rcases h with (h₁ | h₂) | h₃
  · obtain ⟨c, -, hj⟩ := mem_biUnion.mp h₁
    obtain ⟨j, -, heq⟩ := mem_map.mp hj
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨p, -, heq⟩ := mem_map.mp h₂
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨r, -, hi⟩ := mem_biUnion.mp h₃
    obtain ⟨i', hir, heq⟩ := mem_map.mp hi
    change (ComplTwoRectVertex.row i', ComplTwoRectVertex.out r) = (.row i, v) at heq
    have hi_eq : i' = i := ComplTwoRectVertex.row.inj (Prod.mk.inj heq).1
    subst hi_eq
    exact ⟨r, hir, (Prod.mk.inj heq).2.symm⟩

private theorem no_step_from_out {A : Matrix α β Bool} {r : {r : Finset α // #r = 2}}
    {v : ComplTwoRectVertex α β} (h : (.out r, v) ∈ (complTwoRectCircuit A).edges) : False := by
  simp only [complTwoRectCircuit, mem_union] at h
  rcases h with (h₁ | h₂) | h₃
  · obtain ⟨c, -, hj⟩ := mem_biUnion.mp h₁
    obtain ⟨j, -, heq⟩ := mem_map.mp hj
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨p, -, heq⟩ := mem_map.mp h₂
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad
  · obtain ⟨r', -, hi⟩ := mem_biUnion.mp h₃
    obtain ⟨i, -, heq⟩ := mem_map.mp hi
    have hbad := (Prod.mk.inj heq).1
    nomatch hbad

/-- `complTwoRectCircuit A` computes `(twoRectMatrix A).map (! ·)`
([Sergeev2014ORComplement], p. 3). -/
theorem computes_complTwoRectCircuit (A : Matrix α β Bool) :
    (complTwoRectCircuit A).Computes ((twoRectMatrix A).map (! ·)) := by
  intro r c
  refine ⟨fun hrc => ?_, fun ⟨p⟩ => ?_⟩
  · simp only [Matrix.map_apply, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      twoRectMatrix_apply] at hrc
    have hex : ∃ i ∈ r.val, ∃ j ∈ c.val, A i j = false := by
      by_contra hall
      apply hrc
      intro i hir j hjc
      by_contra hnot
      rw [Bool.not_eq_true] at hnot
      exact hall ⟨i, hir, j, hjc, hnot⟩
    obtain ⟨i, hir, j, hjc, hij⟩ := hex
    have he₁ : (.inp c, .col j) ∈ (complTwoRectCircuit A).edges :=
      mem_union_left _ (mem_union_left _
        (mem_biUnion.mpr ⟨c, mem_univ c, mem_map.mpr ⟨j, hjc, rfl⟩⟩))
    have he₂ : (.col j, .row i) ∈ (complTwoRectCircuit A).edges :=
      mem_union_left _ (mem_union_right _
        (mem_map.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij⟩, rfl⟩))
    have he₃ : (.row i, .out r) ∈ (complTwoRectCircuit A).edges :=
      mem_union_right _ (mem_biUnion.mpr ⟨r, mem_univ r, mem_map.mpr ⟨i, hir, rfl⟩⟩)
    exact ⟨.cons he₁ (.cons he₂ (.cons he₃ (.nil _)))⟩
  · obtain ⟨v₁, he₁, ⟨q₁⟩⟩ := p.uncons (fun h => by nomatch h)
    obtain ⟨j, hjc, rfl⟩ := step_from_inp he₁
    obtain ⟨v₂, he₂, ⟨q₂⟩⟩ := q₁.uncons (fun h => by nomatch h)
    obtain ⟨i, hij, rfl⟩ := step_from_col he₂
    obtain ⟨v₃, he₃, ⟨q₃⟩⟩ := q₂.uncons (fun h => by nomatch h)
    obtain ⟨r', hir', rfl⟩ := step_from_row he₃
    have hr_eq : r' = r := by
      by_contra hne
      obtain ⟨_, he₄, -⟩ := q₃.uncons (fun h => hne (ComplTwoRectVertex.out.inj h))
      exact no_step_from_out he₄
    subst hr_eq
    simp only [Matrix.map_apply, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, twoRectMatrix_apply]
    intro hall
    have ht := hall i hir' j hjc
    rw [hij] at ht
    nomatch ht

end ComplTwoRectCircuit

/-- **Sergeev's Lemma 3, upper bound** ([Sergeev2014ORComplement], pp. 2–3): for any `m × m`
Boolean matrix `A` (`m = |α|`, `n = C(m, 2)`),
`orDepthComplexity 3 ((twoRectMatrix A).map (! ·)) ≤ 4 * n + boolMatrixWeight (A.map (! ·))`. -/
theorem orDepthComplexity_three_compl_twoRectMatrix_le [Fintype α] (A : Matrix α α Bool) :
    orDepthComplexity 3 ((twoRectMatrix A).map (! ·)) ≤
      ((4 * (Fintype.card α).choose 2 + boolMatrixWeight (A.map (! ·)) : ℕ) : ℕ∞) := by
  classical
  calc orDepthComplexity 3 ((twoRectMatrix A).map (! ·))
      ≤ ((complTwoRectCircuit A).size : ℕ∞) :=
        (computes_complTwoRectCircuit A).orDepthComplexity_le
          (hasDepthLE_three_complTwoRectCircuit A)
    _ = ((4 * (Fintype.card α).choose 2 + boolMatrixWeight (A.map (! ·)) : ℕ) : ℕ∞) := by
        rw [size_complTwoRectCircuit]
        congr 1
        ring

private theorem two_mul_choose_two (x : ℕ) : 2 * x.choose 2 = x * (x - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self x).two_dvd

private theorem sq_le_three_mul_choose_two {m : ℕ} (hm : 3 ≤ m) : m ^ 2 ≤ 3 * m.choose 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = 3 + t := ⟨m - 3, by omega⟩
  have h2 := two_mul_choose_two (3 + t)
  rw [show 3 + t - 1 = 2 + t by omega] at h2
  nlinarith

/-- **Sergeev's Lemma 3, linear depth-`3` upper bound** ([Sergeev2014ORComplement], pp. 2–3): for
any `m × m` Boolean matrix `A` with `3 ≤ m` (`n = C(m, 2)`),
`orDepthComplexity 3 ((twoRectMatrix A).map (! ·)) ≤ 7 * n`. -/
theorem orDepthComplexity_three_compl_twoRectMatrix_le_seven_mul [Fintype α]
    (A : Matrix α α Bool) (hm : 3 ≤ Fintype.card α) :
    orDepthComplexity 3 ((twoRectMatrix A).map (! ·)) ≤ (7 * (Fintype.card α).choose 2 : ℕ) := by
  refine (orDepthComplexity_three_compl_twoRectMatrix_le A).trans (Nat.cast_le.mpr ?_)
  have hw : boolMatrixWeight (A.map (! ·)) ≤ Fintype.card α ^ 2 := by
    simpa only [sq] using boolMatrixWeight_le_card_mul (A.map (! ·))
  have hch := sq_le_three_mul_choose_two hm
  omega

/-- **Sergeev's Lemma 3, polynomial lower bound** ([Sergeev2014ORComplement], pp. 2–3): if an
`m × m` Boolean matrix `A` is `k`-free and `4 * m ^ 3 ≤ |A| ^ 2`, then
`|A| ^ 4 ≤ 8 * (k * m) ^ 4 * orComplexity (twoRectMatrix A)` (that is,
`OR(twoRectMatrix A) = Ω((|A| / (k m)) ^ 4)`). -/
theorem pow_four_boolMatrixWeight_le_eight_mul_orComplexity_twoRectMatrix [Fintype α]
    {A : Matrix α α Bool} {k : ℕ} (hA : IsRectangleFreeMatrix A k)
    (hdense : 4 * Fintype.card α ^ 3 ≤ boolMatrixWeight A ^ 2) :
    boolMatrixWeight A ^ 4 ≤ 8 * (k * Fintype.card α) ^ 4 * orComplexity (twoRectMatrix A) := by
  have hB : boolMatrixWeight (twoRectMatrix A) ≤
      ((k - 1).choose 2) ^ 2 * orComplexity (twoRectMatrix A) := by
    simpa only [Nat.add_sub_cancel] using
      boolMatrixWeight_le_sq_pred_mul_orComplexity hA.twoRectMatrix
  have hch2 : 2 * (k - 1).choose 2 ≤ k ^ 2 := by
    rw [two_mul_choose_two]
    calc (k - 1) * (k - 1 - 1) ≤ (k - 1) * (k - 1) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
      _ ≤ k * k := Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le k 1)
      _ = k ^ 2 := (sq k).symm
  have hch4 : 4 * ((k - 1).choose 2) ^ 2 ≤ k ^ 4 := by
    calc 4 * ((k - 1).choose 2) ^ 2 = (2 * (k - 1).choose 2) ^ 2 := by ring
      _ ≤ (k ^ 2) ^ 2 := Nat.pow_le_pow_left hch2 2
      _ = k ^ 4 := by ring
  calc boolMatrixWeight A ^ 4
      ≤ 32 * Fintype.card α ^ 4 * boolMatrixWeight (twoRectMatrix A) :=
        pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix A hdense
    _ ≤ 32 * Fintype.card α ^ 4 * (((k - 1).choose 2) ^ 2 * orComplexity (twoRectMatrix A)) :=
        Nat.mul_le_mul_left _ hB
    _ = 8 * (4 * ((k - 1).choose 2) ^ 2) * Fintype.card α ^ 4 *
          orComplexity (twoRectMatrix A) := by ring
    _ ≤ 8 * k ^ 4 * Fintype.card α ^ 4 * orComplexity (twoRectMatrix A) := by gcongr
    _ = 8 * (k * Fintype.card α) ^ 4 * orComplexity (twoRectMatrix A) := by ring

/-- **Sergeev's explicit complement-separation matrix**
`C = (twoRectMatrix (brownMatrix p)).map (! ·)` of dimension `C(p ^ 3, 2) × C(p ^ 3, 2)`
([Sergeev2014ORComplement], Theorem 1(ii), p. 3). -/
@[expose] def sergeevComplementMatrix (p : ℕ) :
    Matrix {r : Finset (Fin 3 → ZMod p) // #r = 2}
      {c : Finset (Fin 3 → ZMod p) // #c = 2} Bool :=
  (twoRectMatrix (brownMatrix p)).map (! ·)

@[simp] theorem map_not_sergeevComplementMatrix (p : ℕ) :
    (sergeevComplementMatrix p).map (! ·) = twoRectMatrix (brownMatrix p) := by
  ext r c
  simp only [sergeevComplementMatrix, Matrix.map_apply, Bool.not_not]

section TheoremOnePartTwo

variable {p : ℕ} [Fact p.Prime]

private theorem card_fin3_zmod : Fintype.card (Fin 3 → ZMod p) = p ^ 3 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

private theorem three_le_card_fin3_zmod (hp : p % 4 = 3) : 3 ≤ Fintype.card (Fin 3 → ZMod p) := by
  rw [card_fin3_zmod]
  have hp3 : 3 ≤ p := by omega
  calc 3 ≤ p ^ 1 := by rw [pow_one]; exact hp3
    _ ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)

/-- **Sergeev's Theorem 1(ii), depth-`3` linear upper bound** ([Sergeev2014ORComplement], pp. 2–3):
for prime `p ≡ 3 (mod 4)` and `n = C(p ^ 3, 2)`,
`orDepthComplexity 3 (sergeevComplementMatrix p) ≤ 7 * n`. -/
theorem orDepthComplexity_three_sergeevComplementMatrix_le (hp : p % 4 = 3) :
    orDepthComplexity 3 (sergeevComplementMatrix p) ≤ (7 * (p ^ 3).choose 2 : ℕ) := by
  simpa only [sergeevComplementMatrix, card_fin3_zmod] using
    orDepthComplexity_three_compl_twoRectMatrix_le_seven_mul (brownMatrix p)
      (three_le_card_fin3_zmod hp)

/-- **Sergeev's Theorem 1(ii), linear `OR`-complexity upper bound** ([Sergeev2014ORComplement],
pp. 1–2): for prime `p ≡ 3 (mod 4)`,
`orComplexity (sergeevComplementMatrix p) ≤ 7 * C(p ^ 3, 2)`. -/
theorem orComplexity_sergeevComplementMatrix_le (hp : p % 4 = 3) :
    orComplexity (sergeevComplementMatrix p) ≤ 7 * (p ^ 3).choose 2 :=
  Nat.cast_le.mp ((orComplexity_le_orDepthComplexity 3 _).trans
    (orDepthComplexity_three_sergeevComplementMatrix_le hp))

/-- **Sergeev's Theorem 1(ii), `2`-freeness of the complement** ([Sergeev2014ORComplement], p. 2):
for prime `p ≡ 3 (mod 4)`, `(sergeevComplementMatrix p).map (! ·)` is `2`-rectangle-free. -/
theorem isRectangleFreeMatrix_compl_sergeevComplementMatrix (hp : p % 4 = 3) :
    IsRectangleFreeMatrix ((sergeevComplementMatrix p).map (! ·)) 2 := by
  rw [map_not_sergeevComplementMatrix]
  exact (isRectangleFreeMatrix_brownMatrix hp).twoRectMatrix

/-- **Sergeev's Theorem 1(ii), exact `OR`-complexity of the complement**
([Sergeev2014ORComplement], pp. 1–2): for prime `p ≡ 3 (mod 4)`,
`orComplexity ((sergeevComplementMatrix p).map (! ·)) =
  boolMatrixWeight ((sergeevComplementMatrix p).map (! ·))`. -/
theorem orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight (hp : p % 4 = 3) :
    orComplexity ((sergeevComplementMatrix p).map (! ·)) =
      boolMatrixWeight ((sergeevComplementMatrix p).map (! ·)) :=
  orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two
    (isRectangleFreeMatrix_compl_sergeevComplementMatrix hp)

/-- **Sergeev's Theorem 1(ii), `Ω(n^{4/3})` complement lower bound** ([Sergeev2014ORComplement],
pp. 1–3): for every prime `p ≡ 3 (mod 4)` and `n = C(p ^ 3, 2)`,
`n ^ 4 ≤ 2 ^ 23 * orComplexity ((sergeevComplementMatrix p).map (! ·)) ^ 3`. -/
theorem choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three
    (hp : p % 4 = 3) :
    ((p ^ 3).choose 2) ^ 4 ≤
      2 ^ 23 * orComplexity ((sergeevComplementMatrix p).map (! ·)) ^ 3 := by
  rw [orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight hp,
    map_not_sergeevComplementMatrix]
  set B_wt := boolMatrixWeight (twoRectMatrix (brownMatrix p))
  by_cases hp3 : p = 3
  · subst hp3
    have hrow : ∀ x : Fin 3 → ZMod 3,
        6 ≤ #(univ.filter fun y => brownMatrix 3 x y = true) :=
      fun x => (card_row_brownMatrix hp x).ge
    have hbound := mul_sub_le_two_mul_choose_mul_boolMatrixWeight_twoRectMatrix
      (brownMatrix 3) hrow
    rw [card_fin3_zmod] at hbound
    have hge32 : 32 ≤ B_wt := by
      norm_num [Nat.choose] at hbound
      omega
    calc ((3 ^ 3).choose 2) ^ 4 ≤ 2 ^ 23 * 32 ^ 3 := by decide
      _ ≤ 2 ^ 23 * B_wt ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hge32 3)
  · have hp5 : p ≠ 5 := by omega
    have hp_ge7 : 7 ≤ p := by
      by_contra hlt
      have hp_prime : p.Prime := Fact.out
      interval_cases p <;> simp_all
    obtain ⟨t, rfl⟩ : ∃ t, p = 7 + t := ⟨p - 7, by omega⟩
    have h4p : 4 * (7 + t) ≤ (7 + t - 1) ^ 2 := by
      rw [show 7 + t - 1 = 6 + t by omega]
      nlinarith
    have hdense : 4 * Fintype.card (Fin 3 → ZMod (7 + t)) ^ 3 ≤
        boolMatrixWeight (brownMatrix (7 + t)) ^ 2 := by
      rw [card_fin3_zmod, boolMatrixWeight_brownMatrix hp]
      calc 4 * ((7 + t) ^ 3) ^ 3 = (7 + t) ^ 8 * (4 * (7 + t)) := by ring
        _ ≤ (7 + t) ^ 8 * (7 + t - 1) ^ 2 := Nat.mul_le_mul_left _ h4p
        _ = ((7 + t) ^ 4 * (7 + t - 1)) ^ 2 := by ring
    have hlem1 := pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix
      (brownMatrix (7 + t)) hdense
    rw [card_fin3_zmod, boolMatrixWeight_brownMatrix hp] at hlem1
    have hp12_pos : 0 < (7 + t) ^ 12 := by positivity
    have h32 : (7 + t) ^ 4 * (7 + t - 1) ^ 4 ≤ 32 * B_wt := by
      refine Nat.le_of_mul_le_mul_left (c := (7 + t) ^ 12) ?_ hp12_pos
      calc (7 + t) ^ 12 * ((7 + t) ^ 4 * (7 + t - 1) ^ 4)
          = ((7 + t) ^ 4 * (7 + t - 1)) ^ 4 := by ring
        _ ≤ 32 * ((7 + t) ^ 3) ^ 4 * B_wt := hlem1
        _ = (7 + t) ^ 12 * (32 * B_wt) := by ring
    have hp_le_2pred : 7 + t ≤ 2 * (7 + t - 1) := by omega
    have hp4_le : (7 + t) ^ 4 ≤ 16 * (7 + t - 1) ^ 4 :=
      (Nat.pow_le_pow_left hp_le_2pred 4).trans_eq (by ring)
    have hp8_le : (7 + t) ^ 8 ≤ 512 * B_wt := by
      calc (7 + t) ^ 8 = (7 + t) ^ 4 * (7 + t) ^ 4 := by ring
        _ ≤ (7 + t) ^ 4 * (16 * (7 + t - 1) ^ 4) := Nat.mul_le_mul_left _ hp4_le
        _ = 16 * ((7 + t) ^ 4 * (7 + t - 1) ^ 4) := by ring
        _ ≤ 16 * (32 * B_wt) := Nat.mul_le_mul_left 16 h32
        _ = 512 * B_wt := by ring
    have h2n_le : 2 * ((7 + t) ^ 3).choose 2 ≤ (7 + t) ^ 6 := by
      rw [two_mul_choose_two]
      exact (Nat.mul_le_mul_left _ (Nat.sub_le _ 1)).trans_eq (by ring)
    have h16n4 : 16 * (((7 + t) ^ 3).choose 2) ^ 4 ≤ 2 ^ 27 * B_wt ^ 3 := by
      calc 16 * (((7 + t) ^ 3).choose 2) ^ 4
          = (2 * ((7 + t) ^ 3).choose 2) ^ 4 := by ring
        _ ≤ ((7 + t) ^ 6) ^ 4 := Nat.pow_le_pow_left h2n_le 4
        _ = ((7 + t) ^ 8) ^ 3 := by ring
        _ ≤ (512 * B_wt) ^ 3 := Nat.pow_le_pow_left hp8_le 3
        _ = 2 ^ 27 * B_wt ^ 3 := by ring
    linarith

end TheoremOnePartTwo

/-- **Sergeev's Theorem 1(ii), unbounded `Fin n × Fin n` family** ([Sergeev2014ORComplement],
pp. 1–2): for arbitrarily large `n`, there is an `n × n` Boolean matrix `C` with
`OR_3(C) ≤ 7 * n`, `OR(C) ≤ 7 * n`, `C̄` `2`-rectangle-free, `OR(C̄) = |C̄|`, and
`n ^ 4 ≤ 2 ^ 23 * OR(C̄) ^ 3`. -/
theorem exists_gt_sergeev_or_complement_separation (N : ℕ) :
    ∃ (n : ℕ) (C : Matrix (Fin n) (Fin n) Bool),
      N < n ∧
      orDepthComplexity 3 C ≤ (7 * n : ℕ) ∧
      orComplexity C ≤ 7 * n ∧
      IsRectangleFreeMatrix (C.map (! ·)) 2 ∧
      orComplexity (C.map (! ·)) = boolMatrixWeight (C.map (! ·)) ∧
      n ^ 4 ≤ 2 ^ 23 * orComplexity (C.map (! ·)) ^ 3 := by
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (N + 3) (q := 4) (a := 3) (by decide) (by decide)
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp : p % 4 = 3 := hp_mod
  set n := (p ^ 3).choose 2
  have hcard : Fintype.card {s : Finset (Fin 3 → ZMod p) // #s = 2} = n := by
    rw [card_twoSubsets, card_fin3_zmod]
  let e : {s : Finset (Fin 3 → ZMod p) // #s = 2} ≃ Fin n :=
    (Fintype.equivFin _).trans (finCongr hcard)
  let C : Matrix (Fin n) (Fin n) Bool := Matrix.reindex e e (sergeevComplementMatrix p)
  have hC_compl : C.map (! ·) = Matrix.reindex e e ((sergeevComplementMatrix p).map (! ·)) :=
    rfl
  have hn_gt : N < n := by
    have hp3 : p ≤ p ^ 3 := Nat.le_self_pow (by norm_num) p
    have h2n : 2 * n = p ^ 3 * (p ^ 3 - 1) := two_mul_choose_two (p ^ 3)
    have := Nat.mul_le_mul_left (p ^ 3) (show 2 ≤ p ^ 3 - 1 by omega)
    omega
  refine ⟨n, C, hn_gt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orDepthComplexity_reindex]
    exact orDepthComplexity_three_sergeevComplementMatrix_le hp
  · rw [orComplexity_reindex]
    exact orComplexity_sergeevComplementMatrix_le hp
  · rw [hC_compl, isRectangleFreeMatrix_reindex]
    exact isRectangleFreeMatrix_compl_sergeevComplementMatrix hp
  · rw [hC_compl, orComplexity_reindex, boolMatrixWeight_reindex]
    exact orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight hp
  · rw [hC_compl, orComplexity_reindex]
    exact choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three hp

end Cslib.Circuits
