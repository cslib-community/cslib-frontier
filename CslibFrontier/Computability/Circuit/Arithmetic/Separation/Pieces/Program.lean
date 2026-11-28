/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SlpCostPow
public import CslibFrontier.Foundations.Combinatorics.StagedTree
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
# The pieces of a tree by stages are computed by a program

Let `T x` be trees by stages (`Cslib.StagedTree`) on the nodes `α`, one for every input `x` of a
straight-line program, with the same stages, depth `dp` and root. If a program computes the
indicators of the parents in `T x` and the weights `u x` of the nodes (the weights `g` do not
depend on `x`), then `2 dp + 4` more stages of `Y ^ 12` gates compute the pieces of all nodes
(`Cslib.Circuits.Arithmetic.Separation.Pieces.pieces_stage`): `dp + 1` stages for the ancestors,
one for the heads, `dp + 1` for the heads of the pieces and one for the pieces.

## Main results

* `Cslib.Circuits.Arithmetic.Separation.Pieces.pieces_stage`: the pieces take `2 dp + 4` stages.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2, p. 52, and its proof (the heavy nodes and the pieces are computed from the
  parents and the numbers `u_p`, p. 53); module `Paper.HeavyProg`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Pieces

open Finset Cslib.FunctionalGraph

variable {Inp : Type} {D Y n p c : ℕ} {inp : Fin n → Inp → Fin D} {H : Set (Inp → ℕ)}
  {α : Type*}

/-- Whether `absorb (f x) (G x) q = q'` is decided in `Y ^ 3` steps from the indicators of `G x q`
and of `f x q = q'`. -/
private theorem costP_absorb (hY : StepBase D Y) {G : Inp → α → Prop}
    [∀ x, DecidablePred (G x)] {f : Inp → α → α} (hG : ∀ q, {x | G x q}.indicator 1 ∈ H)
    (hf : ∀ q q', {x | f x q = q'}.indicator 1 ∈ H) (q q' : α) :
    CostP D H (Y ^ 3) fun x => absorb (f x) (G x) q = q' :=
  (hY.or (hY.and (CostP.of_mem (hG q)) (hY.constP (q = q')))
    (hY.and (hY.not (CostP.of_mem (hG q))) (CostP.of_mem (hf q q')))).congr fun x => by
    unfold absorb
    split_ifs with h <;> simp [h]

variable {T : Inp → StagedTree α} {st : α → ℕ} {dp : ℕ} {rt : α} {g : α → ℕ} {u : Inp → α → ℕ}
  {M Yh k : ℕ}

private theorem costP_below (hY : StepBase D Y) (hst : ∀ x, (T x).stage = st)
    (hdp : ∀ x, (T x).depth = dp)
    (hit : ∀ j < dp + 1, ∀ q q', {x | (T x).parent^[j] q = q'}.indicator 1 ∈ H) (q q' : α)
    {a : ℕ} : CostP D H (Y ^ a) fun x => (T x).Below q q' := by
  by_cases h : st q ≤ st q' ∧ st q' - st q < dp + 1
  · exact (CostP.of_mem (hit _ h.2 q q')).congr fun x => by
      simp only [StagedTree.Below, hst, h.1, true_and]
  · refine (hY.constP False).congr fun x => ⟨False.elim, fun hb => h ?_⟩
    have := (T x).stage_le q'
    simp only [StagedTree.Below, hst, hdp] at hb this
    omega

variable [Fintype α]

/-- `t` stages compute the indicators of the first `t` iterates of maps `f x` whose indicators are
decided in `Y ^ 3` steps. -/
private theorem iterate_stage (hY : StepBase D Y) (hα : Fintype.card α ≤ Y) {f : Inp → α → α}
    (hS : SlpN inp (p + c * Y ^ 12) H) (hf : ∀ q q', CostP D H (Y ^ 3) fun x => f x q = q')
    (t : ℕ) : ∃ H', SlpN inp (p + (c + t) * Y ^ 12) H' ∧ H ⊆ H' ∧
      ∀ j < t, ∀ q q', {x | (f x)^[j] q = q'}.indicator 1 ∈ H' := by
  induction t with
  | zero => exact ⟨H, by simpa using hS, subset_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    have hc (q : α × α) : CostP D H0 (Y ^ 6) fun x => (f x)^[t] q.1 = q.2 := by
      rcases t with _ | t
      · exact hY.constP (q.1 = q.2)
      refine (hY.exists_univ hα fun q' => hY.and (CostP.of_mem (f0 t t.lt_succ_self q.1 q'))
        (costP_iff.2 ((costP_iff.1 (hf q' q.2)).weaken u0))).congr fun x => ?_
      rw [Function.iterate_succ_apply']
      exact ⟨fun ⟨_, h1, h2⟩ => h1 ▸ h2, fun h => ⟨_, rfl, h⟩⟩
    obtain ⟨H1, s1, u1, f1⟩ := hY.stage s0 (fun q : α × α => {x | (f x)^[t] q.1 = q.2}.indicator 1)
      (by simpa [pow_two] using Nat.mul_le_mul hα hα) (fun q => costP_iff.1 (hc q)) (e := 2)
      (by norm_num)
    refine ⟨H1, s1, u0.trans u1, fun j hj q q' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact u1 (f0 j hj q q')
    · exact f1 (q, q')

/-- A sum over the nodes of values at most `Y`, each kept or replaced by `0` by a property. -/
private theorem cost_sum_ite (hY : StepBase D Y) (hα : Fintype.card α ≤ Y) {a : ℕ}
    {P : α → Inp → Prop} [∀ q x, Decidable (P q x)] {f : α → Inp → ℕ}
    (hP : ∀ q, CostP D H (Y ^ a) (P q)) (hf : ∀ q, Cost D H (Y ^ a) (f q))
    (hb : ∀ q x, f q x ≤ Y) :
    Cost D H (Y ^ (a + 2 + 2)) fun x => ∑ q, if P q x then f q x else 0 := by
  refine hY.sum univ (by simpa using hα) (fun q _ => hY.ite (hP q) (hf q) (hY.const 0 hY.zero_lt)
    (fun x => hY.lt_of_le (hb q x)) fun _ => hY.zero_lt) fun x => hY.lt_of_le_two_mul_pow_three ?_
  have := hY.pos
  calc ∑ q, (if P q x then f q x else 0) ≤ ∑ _q : α, Y :=
        sum_le_sum fun q _ => by split_ifs <;> simp [hb]
    _ ≤ Y * Y := by simpa using Nat.mul_le_mul_right Y hα
    _ ≤ 2 * Y ^ 3 := by nlinarith [Nat.mul_le_mul_left (Y * Y) this]

variable [LinearOrder α]

private theorem costP_heavy (hY : StepBase D Y) (hα : Fintype.card α ≤ Y)
    (hst : ∀ x, (T x).stage = st) (hdp : ∀ x, (T x).depth = dp) (hrt : ∀ x, (T x).root = rt)
    (hit : ∀ j < dp + 1, ∀ q q', {x | (T x).parent^[j] q = q'}.indicator 1 ∈ H)
    (hg : ∀ q, g q ≤ Y) (hu : ∀ q, (fun x => u x q) ∈ H) (hub : ∀ x q, u x q ≤ Y) (q : α) :
    CostP D H (Y ^ 5) fun x => (T x).Heavy g (u x) M Yh k q := by
  have hsum (f : Inp → α → ℕ) (hf : ∀ q, Cost D H (Y ^ 0) fun x => f x q)
      (hb : ∀ x q, f x q ≤ Y) : Cost D H (Y ^ 4) fun x => (T x).sumBelow (f x) q :=
    (cost_sum_ite hY hα (fun q' => costP_below hY hst hdp hit q' q) hf fun q' x => hb x q').congr
      fun x => by simp only [StagedTree.sumBelow, sum_filter]
  by_cases hq : q = rt
  · exact (hY.constP True).congr fun x =>
      ⟨fun _ => Or.inl (hq.trans (hrt x).symm), fun _ => trivial⟩
  · refine (hY.rel (fun a b => 8 * M * Yh < k * (a * (2 * Yh) + b * (4 * M)))
      (hsum (fun _ => g) (fun q => hY.const _ (hY.lt_of_le (hg q))) fun _ => hg)
      (hsum u (fun q => Cost.of_mem (hu q)) hub)).congr fun x => ?_
    simp only [StagedTree.Heavy, hrt, hq, false_or]

/-- **The pieces are computed**: from a program that computes the indicators of the parents in the
trees `T x` and the weights `u x` (and with values below `Y`), `2 dp + 4` more stages of `Y ^ 12`
gates compute the pieces of all nodes, for the weights `g` and `u x`, the budgets `M` and `Yh` and
the number `k`. -/
theorem pieces_stage (hY : StepBase D Y) (hα : Fintype.card α ≤ Y)
    (hst : ∀ x, (T x).stage = st) (hdp : ∀ x, (T x).depth = dp) (hrt : ∀ x, (T x).root = rt)
    (hS : SlpN inp (p + c * Y ^ 12) H) (hpar : ∀ q q', {x | (T x).parent q = q'}.indicator 1 ∈ H)
    (hu : ∀ q, (fun x => u x q) ∈ H) (hg : ∀ q, g q ≤ Y) (hub : ∀ x q, u x q ≤ Y) :
    ∃ H', SlpN inp (p + (c + 2 * dp + 4) * Y ^ 12) H' ∧ H ⊆ H' ∧
      ∀ q, (fun x => (T x).piece g (u x) M Yh k q) ∈ H' := by
  obtain ⟨H1, s1, u1, f1⟩ := iterate_stage hY hα (f := fun x => (T x).parent) hS
    (fun q q' => CostP.of_mem (hpar q q')) (dp + 1)
  have hhead (q : α) : CostP D H1 (Y ^ 8) fun x => (T x).IsHead g (u x) M Yh k q := by
    by_cases hq : q = rt
    · exact (hY.constP True).congr fun x =>
        ⟨fun _ => Or.inl (hq.trans (hrt x).symm), fun _ => trivial⟩
    · refine (hY.exists_univ hα fun q' => hY.and (CostP.of_mem (u1 (hpar q q')))
        (costP_heavy (M := M) (Yh := Yh) (k := k) hY hα hst hdp hrt f1 hg (fun q => u1 (hu q))
          hub q')).congr fun x => ?_
      simp only [StagedTree.IsHead, hrt, hq, false_or, exists_eq_left']
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1
    (fun q => {x | (T x).IsHead g (u x) M Yh k q}.indicator 1) (e := 1) (by simpa using hα)
    (fun q => costP_iff.1 (hhead q)) (by norm_num)
  obtain ⟨H3, s3, u3, f3⟩ := iterate_stage hY hα s2
    (f := fun x => absorb (T x).parent ((T x).IsHead g (u x) M Yh k))
    (costP_absorb hY f2 fun q q' => u2 (u1 (hpar q q'))) (dp + 1)
  have hrank (q : α) : Cost D H3 (Y ^ 2) fun x => (T x).headRank g (u x) M Yh k q :=
    (hY.card_filter (univ.filter (· < q)) ((card_filter_le _ _).trans (by simpa using hα))
      fun q' _ => CostP.of_mem (u3 (f2 q'))).congr fun x => by
      simp only [StagedTree.headRank, filter_filter]
  obtain ⟨H4, s4, u4, f4⟩ := hY.stage s3 (fun q x => (T x).piece g (u x) M Yh k q) (e := 1)
    (by simpa using hα) (fun q => (cost_sum_ite hY hα
      (fun q' => CostP.of_mem (f3 (dp - st q) (by omega) q q')) hrank
      fun q' x => (card_filter_le _ _).trans (by simpa using hα)).congr fun x => by
        rw [sum_ite_eq_of_mem _ _ _ (mem_univ _)]
        simp only [StagedTree.piece, StagedTree.pieceHead, hdp, hst]) (by norm_num)
  exact ⟨H4, by rwa [show c + 2 * dp + 4 = c + (dp + 1) + 1 + (dp + 1) + 1 by omega],
    u1.trans (u2.trans (u3.trans u4)), f4⟩

end Cslib.Circuits.Arithmetic.Separation.Pieces
