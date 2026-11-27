/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.Submodular.ValueQuery
public import CslibFrontier.Algorithms.Lean.Submodular.Queyranne
public import Cslib.Algorithms.Lean.Query.Bounds
-- Reads private `eraseBlock` and block-partition helpers (`nodup_of_pairwise_disjoint_nonempty`,
-- `mergeBlocks_nonempty_disjoint`, `length_mergeBlocks`, `mem_eraseBlock_iff`, `length_eraseBlock`,
-- `nodup_fst_eraseBlock`) from `Algorithms.Lean.Submodular.Queyranne`.
import all CslibFrontier.Algorithms.Lean.Submodular.Queyranne
import CslibFrontier.Foundations.Data.List.EraseDups
import Mathlib.Tactic.Linarith

/-!
# Value-Oracle Query Complexity of Queyranne's Algorithm

This module lifts `queyranneM` into `FreeM (ValueQuery V β)` as `queyranneQuery`, proves that
`FreeM.eval` recovers the pure `queyranne` algorithm against any value oracle, and establishes both
the exact query count and the `O(|V|³)` `Cslib.Query.UpperBound` against arbitrary adversarial
value oracles ([Queyranne1998]):

1. **Exact query identity** (`countQueries_queyranneQuery_eq`): when `2 ≤ vs.toFinset.card`,
   every execution of `queyranneQuery vs` against any `oracle` uses `Q` queries where
   `6 * Q + 12 * n = n * (n + 1) * (n + 2) + 6` for `n = vs.toFinset.card` (hence
   `Q = (n³ + 3n² - 10n + 6) / 6`), and `Q = 1` when `vs.toFinset.card < 2`.
2. **Cubic value-oracle upper bound** (`three_mul_countQueries_queyranneQuery_le`,
   `countQueries_queyranneQuery_le`, `queyranneQuery_upperBound`): for `2 ≤ n`,
   `3 * Q ≤ n³` (hence `Q ≤ n³ ≤ vs.length³`), giving `UpperBound queyranneQuery List.length
   (fun n => n ^ 3 + 1)` unconditionally over all `List V`.
3. **End-to-end oracle optimality**: `eval_queyranneQuery_spec` combines `queyranne_spec` with
   `eval_queyranneQuery` against `ValueQuery.oracleOf` for symmetric submodular functions.

## Main definitions

* `Cslib.Query.queyranneQuery`: Queyranne's minimization algorithm in `FreeM (ValueQuery V β)`.

## Main results

* `eval_queyranneQuery`: agreement with pure `queyranne`.
* `countQueries_queyranneQuery_eq`, `three_mul_countQueries_queyranneQuery_le`,
  `countQueries_queyranneQuery_le`, `queyranneQuery_upperBound`: exact query count and `O(|V|³)`
  upper bound.
* `eval_queyranneQuery_spec`: global symmetric submodular minimization guarantee via value oracle.

## References

* [M. Queyranne, *Minimizing symmetric submodular functions*][Queyranne1998]
-/

public section

open Cslib.Algorithms.Lean.Submodular
open Cslib.WeightedCut (IsNonTrivialCut)

namespace Cslib.Query

/-- Value-oracle query tree for Queyranne's symmetric submodular minimization algorithm. -/
@[expose] def queyranneQuery {V β : Type} [DecidableEq V] [Add β] [LT β] [DecidableLT β]
    (vs : List V) : FreeM (ValueQuery V β) (QCutResult V β) :=
  queyranneM ValueQuery.ask vs

section EvalAndCount

variable {V β : Type}

private theorem countQueries_qSingletonsM
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (bs : List (Finset V)) :
    (qSingletonsM (ValueQuery.ask (α := V) (β := β)) bs).countQueries oracle = bs.length := by
  induction bs with
  | nil => simp [qSingletonsM]
  | cons b bs ih =>
    simp [qSingletonsM, ih, Nat.add_comm]

private theorem map_fst_eval_qSingletonsM
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (bs : List (Finset V)) :
    ((qSingletonsM (ValueQuery.ask (α := V) (β := β)) bs).eval oracle).map Prod.fst = bs := by
  induction bs with
  | nil => simp [qSingletonsM]
  | cons b bs ih => simp [qSingletonsM, ih]

variable [DecidableEq V] [Add β] [LT β] [DecidableLT β]

/-- Evaluating `queyranneQuery` against `oracle` agrees with `queyranne` on
`fun S => oracle (.value S)`. -/
@[simp] theorem eval_queyranneQuery
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (vs : List V) :
    (queyranneQuery vs).eval oracle = queyranne (fun S => oracle (.value S)) vs :=
  Id.pure_injective <| by
    simp [queyranneQuery, queyranne,
      (FreeM.isMonadHom_pure_eval oracle).map_queyranneM _ vs]

theorem eval_queyranneQuery_oracleOf
    (f : Finset V → β) (vs : List V) :
    (queyranneQuery vs).eval (ValueQuery.oracleOf f) = queyranne f vs := by
  simp

private theorem countQueries_qScanM
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (A best : Finset V) (sBest vBest : β) (cs : List (Finset V × β)) :
    (qScanM ValueQuery.ask A best sBest vBest cs).countQueries oracle = cs.length := by
  induction cs generalizing best sBest vBest with
  | nil => simp [qScanM]
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [qScanM, FreeM.countQueries_bind, ValueQuery.countQueries_ask, ValueQuery.eval_ask]
    by_cases h : oracle (.value (A ∪ b)) + sBest < vBest + sb <;> simp [h, ih, Nat.add_comm]

private theorem eval_qScanM_best_mem
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (A best : Finset V) (sBest vBest : β) (cs : List (Finset V × β)) :
    ∃ sb, (((qScanM ValueQuery.ask A best sBest vBest cs).eval oracle).best, sb) ∈
      (best, sBest) :: cs := by
  induction cs generalizing best sBest vBest with
  | nil => exact ⟨sBest, List.mem_cons_self⟩
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [qScanM, FreeM.eval_bind, ValueQuery.eval_ask]
    by_cases h : oracle (.value (A ∪ b)) + sBest < vBest + sb <;> simp only [h, ↓reduceIte]
    · exact (ih b sb _).imp fun _ => List.mem_cons_of_mem _
    · exact (ih best sBest vBest).imp fun _ hs => (List.mem_cons.mp hs).elim
        (List.mem_cons.mpr ∘ .inl) (List.mem_cons_of_mem _ ∘ List.mem_cons_of_mem _)

private theorem eraseBlock_qScanM_eq_cons
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (A : Finset V) (c₀ c₁ : Finset V × β) (cs : List (Finset V × β)) :
    ∃ sBest d₀ ds,
      (((qScanM ValueQuery.ask A c₀.1 c₀.2
        (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best, sBest) ∈ c₀ :: c₁ :: cs ∧
      eraseBlock ((qScanM ValueQuery.ask A c₀.1 c₀.2
        (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best (c₀ :: c₁ :: cs) = d₀ :: ds ∧
      ds.length = cs.length := by
  obtain ⟨sBest, hsBest⟩ :=
    eval_qScanM_best_mem oracle A c₀.1 c₀.2 (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)
  have hlen_er := length_eraseBlock ⟨sBest, hsBest⟩
  cases her : eraseBlock ((qScanM ValueQuery.ask A c₀.1 c₀.2
      (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best (c₀ :: c₁ :: cs) with
  | nil => simp [her] at hlen_er
  | cons d₀ ds =>
    refine ⟨sBest, d₀, ds, hsBest, rfl, ?_⟩
    simp only [her, List.length_cons] at hlen_er; omega

private theorem countQueries_qSearchStepsM_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι) :
    ∀ (k : ℕ) (A prev : Finset V) (c₀ : Finset V × β) (cs : List (Finset V × β)),
      cs.length = k →
      2 * (qSearchStepsM ValueQuery.ask k A prev c₀ cs).countQueries oracle = k * (k + 3)
  | 0, _, _, _, _, _ => by simp [qSearchStepsM]
  | _ + 1, _, _, _, [], hlen => by simp at hlen
  | k + 1, A, prev, c₀, c₁ :: cs, hlen => by
    obtain ⟨_, d₀, ds, -, her, hds_len⟩ := eraseBlock_qScanM_eq_cons oracle A c₀ c₁ cs
    have hds : ds.length = k := by simp only [List.length_cons] at hlen; omega
    simp only [qSearchStepsM, FreeM.countQueries_bind, ValueQuery.countQueries_ask,
      ValueQuery.eval_ask, countQueries_qScanM, her, hlen]
    have ih := countQueries_qSearchStepsM_eq oracle k
      (A ∪ ((qScanM ValueQuery.ask A c₀.1 c₀.2
        (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best)
      ((qScanM ValueQuery.ask A c₀.1 c₀.2
        (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best d₀ ds hds
    nlinarith

private theorem eval_qSearchStepsM_spec
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {blocks : List (Finset V)} :
    ∀ (k : ℕ) (A prev : Finset V) (c₀ : Finset V × β) (cs : List (Finset V × β)),
      cs.length = k →
      prev ∈ blocks →
      (∀ p ∈ c₀ :: cs, p.1 ∈ blocks) →
      ((c₀ :: cs).map Prod.fst).Nodup →
      prev ∉ (c₀ :: cs).map Prod.fst →
      let res := (qSearchStepsM ValueQuery.ask k A prev c₀ cs).eval oracle
      res.fst ∈ blocks ∧ res.snd ∈ blocks ∧ res.fst ≠ res.snd
  | 0, _, prev, (t, st), _, _, hprev, hmem, _, hnot => by
    have ht : t ∈ blocks := hmem (t, st) List.mem_cons_self
    have hne : prev ≠ t := fun h => hnot (by simp [h])
    simpa [qSearchStepsM] using ⟨hprev, ht, hne⟩
  | _ + 1, _, _, _, [], hlen, _, _, _, _ => by simp at hlen
  | k + 1, A, prev, c₀, c₁ :: cs, hlen, _, hmem, hnd, _ => by
    obtain ⟨sBest, d₀, ds, hsBest, her, hds_len⟩ := eraseBlock_qScanM_eq_cons oracle A c₀ c₁ cs
    set best := ((qScanM ValueQuery.ask A c₀.1 c₀.2
      (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).best
    have hsub' : ∀ p ∈ d₀ :: ds, p ∈ c₀ :: c₁ :: cs ∧ p.1 ≠ best := fun p hp =>
      (mem_eraseBlock_iff hnd).mp (her ▸ hp)
    have hds : ds.length = k := by simp only [List.length_cons] at hlen; omega
    have ih := eval_qSearchStepsM_spec oracle k (A ∪ best) best d₀ ds hds
      (hmem (best, sBest) hsBest) (fun p hp => hmem p (hsub' p hp).1)
      (her ▸ nodup_fst_eraseBlock best hnd)
      (fun hin => by obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hin; exact (hsub' p hp).2 hpeq)
    simpa [qSearchStepsM, her, best] using ih

omit [DecidableEq V] [Add β] [LT β] [DecidableLT β] in
private theorem eval_qSingletonsM_cons_eq_cons
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (b₁ : Finset V) (bs : List (Finset V)) :
    ∃ c₀ cs, (qSingletonsM (ValueQuery.ask (α := V) (β := β)) (b₁ :: bs)).eval oracle =
      c₀ :: cs ∧ (c₀ :: cs).map Prod.fst = b₁ :: bs ∧ cs.length = bs.length := by
  have hmap := map_fst_eval_qSingletonsM oracle (b₁ :: bs)
  cases hc : (qSingletonsM (ValueQuery.ask (α := V) (β := β)) (b₁ :: bs)).eval oracle with
  | nil => rw [hc] at hmap; simp at hmap
  | cons c₀ cs =>
    rw [hc] at hmap
    exact ⟨c₀, cs, rfl, hmap, by
      have hl := congrArg List.length hmap
      simp only [List.length_map, List.length_cons] at hl; omega⟩

private theorem countQueries_qSearchM_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (b₀ b₁ : Finset V) (bs : List (Finset V)) :
    2 * (qSearchM ValueQuery.ask b₀ b₁ bs).countQueries oracle + 4 =
      (bs.length + 2) * (bs.length + 3) := by
  obtain ⟨c₀, cs, hc, -, hlen⟩ := eval_qSingletonsM_cons_eq_cons oracle b₁ bs
  have hsteps := countQueries_qSearchStepsM_eq oracle bs.length b₀ b₀ c₀ cs hlen
  simp only [qSearchM, FreeM.countQueries_bind, countQueries_qSingletonsM, List.length_cons, hc]
  nlinarith

private theorem eval_qSearchM_mem
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    {b₀ b₁ : Finset V} {bs : List (Finset V)} (hnd : (b₀ :: b₁ :: bs).Nodup) :
    let res := (qSearchM ValueQuery.ask b₀ b₁ bs).eval oracle
    res.fst ∈ b₀ :: b₁ :: bs ∧ res.snd ∈ b₀ :: b₁ :: bs ∧ res.fst ≠ res.snd := by
  obtain ⟨c₀, cs, hc, hmap, hlen⟩ := eval_qSingletonsM_cons_eq_cons oracle b₁ bs
  rw [List.nodup_cons] at hnd
  have hc_mem : ∀ p ∈ c₀ :: cs, p.1 ∈ b₀ :: b₁ :: bs := fun p hp =>
    List.mem_cons_of_mem b₀ (hmap ▸ List.mem_map_of_mem hp)
  simpa only [qSearchM, FreeM.eval_bind, hc] using
    eval_qSearchStepsM_spec oracle bs.length b₀ b₀ c₀ cs hlen
      List.mem_cons_self hc_mem (hmap ▸ hnd.2) (hmap ▸ hnd.1)

private theorem countQueries_queyranneRecM_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι) :
    ∀ (steps : ℕ) (blocks : List (Finset V)),
      (∀ b ∈ blocks, b.Nonempty) → blocks.Pairwise Disjoint →
      blocks.length = steps + 2 →
      6 * (queyranneRecM ValueQuery.ask steps blocks).countQueries oracle + 12 * (steps + 2) =
        (steps + 2) * (steps + 3) * (steps + 4) + 6
  | 0, blocks, _, _, hlen => by
    rcases blocks with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩ <;> simp at hlen
    simp [queyranneRecM]
  | steps + 1, blocks, hne, hdisj, hlen => by
    rcases blocks with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩ <;> simp at hlen
    have hnd := nodup_of_pairwise_disjoint_nonempty hne hdisj
    have hsearch := eval_qSearchM_mem oracle hnd
    set sr := (qSearchM ValueQuery.ask b₀ b₁ bs).eval oracle
    have hmerge := mergeBlocks_nonempty_disjoint hne hdisj hsearch.1 hsearch.2.1 hsearch.2.2
    have hlen' : (mergeBlocks sr.fst sr.snd (b₀ :: b₁ :: bs)).length = steps + 2 := by
      have hm := length_mergeBlocks hsearch.1 hsearch.2.1 hsearch.2.2
      simp only [List.length_cons] at hm
      omega
    have ih := countQueries_queyranneRecM_eq oracle steps
      (mergeBlocks sr.fst sr.snd (b₀ :: b₁ :: bs)) hmerge.1 hmerge.2 hlen'
    have hq := countQueries_qSearchM_eq oracle b₀ b₁ bs
    have hbs : bs.length = steps + 1 := by omega
    rw [hbs] at hq
    simp only [queyranneRecM, FreeM.countQueries_bind]
    split_ifs <;> simp only [FreeM.countQueries_pure, add_zero] <;> linarith

/-- **Exact value-oracle query complexity** ([Queyranne1998]): when `2 ≤ n := vs.toFinset.card`,
against any value oracle `queyranneQuery vs` performs `Q` queries satisfying
`6 * Q + 12 * n = n * (n + 1) * (n + 2) + 6`. -/
theorem countQueries_queyranneQuery_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : 2 ≤ vs.toFinset.card) :
    6 * (queyranneQuery vs).countQueries oracle + 12 * vs.toFinset.card =
      vs.toFinset.card * (vs.toFinset.card + 1) * (vs.toFinset.card + 2) + 6 := by
  have hu_len : vs.eraseDups.length = vs.toFinset.card := List.length_eraseDups vs
  have hne : ∀ b ∈ vs.eraseDups.map ({·} : V → Finset V), b.Nonempty :=
    List.forall_mem_map.mpr fun v _ => Finset.singleton_nonempty v
  have hdisj : (vs.eraseDups.map ({·} : V → Finset V)).Pairwise Disjoint :=
    List.pairwise_map.mpr ((List.nodup_eraseDups vs).imp Finset.disjoint_singleton.mpr)
  have hm : vs.toFinset.card = (vs.eraseDups.length - 2) + 2 := by omega
  rw [hm]
  exact countQueries_queyranneRecM_eq oracle (vs.eraseDups.length - 2) _ hne hdisj
    (by rw [List.length_map]; omega)

/-- On degenerate inputs with fewer than two distinct elements, `queyranneQuery vs` makes `1`
query (`∅`). -/
theorem countQueries_queyranneQuery_eq_one_of_lt_two
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : vs.toFinset.card < 2) :
    (queyranneQuery vs).countQueries oracle = 1 := by
  have hlen : vs.eraseDups.length < 2 := (List.length_eraseDups vs).symm ▸ hvs
  simp only [queyranneQuery, queyranneM]
  rcases hu : vs.eraseDups with _ | ⟨a, _ | ⟨b, bs⟩⟩ <;> simp_all [queyranneRecM]

/-- When `2 ≤ vs.toFinset.card`, `3 * countQueries ≤ vs.toFinset.card ^ 3` against any oracle. -/
theorem three_mul_countQueries_queyranneQuery_le
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : 2 ≤ vs.toFinset.card) :
    3 * (queyranneQuery vs).countQueries oracle ≤ vs.toFinset.card ^ 3 := by
  have heq := countQueries_queyranneQuery_eq oracle hvs
  set n := vs.toFinset.card
  rcases Nat.eq_or_lt_of_le hvs with heq2 | hn
  · rw [← heq2] at heq ⊢; omega
  · nlinarith

/-- Pointwise cubic upper bound valid for all input lists `vs`, including degenerate lists with
`vs.toFinset.card < 2`. -/
theorem countQueries_queyranneQuery_le
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (vs : List V) :
    (queyranneQuery vs).countQueries oracle ≤ vs.length ^ 3 + 1 := by
  by_cases hvs : 2 ≤ vs.toFinset.card
  · have hcube : (queyranneQuery vs).countQueries oracle ≤ vs.toFinset.card ^ 3 :=
      (Nat.le_mul_of_pos_left _ (by omega)).trans
        (three_mul_countQueries_queyranneQuery_le oracle hvs)
    exact (hcube.trans (Nat.pow_le_pow_left (List.toFinset_card_le vs) 3)).trans (Nat.le_succ _)
  · rw [countQueries_queyranneQuery_eq_one_of_lt_two oracle (Nat.lt_of_not_le hvs)]
    exact Nat.le_add_left 1 _

/-- Uniform `Cslib.Query.UpperBound`: `queyranneQuery` uses `n³ + 1 = O(|V|³)` value queries on
inputs of list length at most `n` against every oracle. -/
theorem queyranneQuery_upperBound :
    UpperBound (queyranneQuery (V := V) (β := β)) List.length (fun n => n ^ 3 + 1) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.add_le_add_right (Nat.pow_le_pow_left h 3) 1)
    countQueries_queyranneQuery_le

end EvalAndCount

section OracleMinimization

/-- End-to-end oracle optimality of `queyranneQuery`: when `2 ≤ |V|`, evaluating against
`ValueQuery.oracleOf f` returns a global minimizer of any symmetric submodular function `f`. -/
theorem eval_queyranneQuery_spec {V β : Type} [DecidableEq V] [Fintype V]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset V → β} (hf : IsSubmodular f) (hsym : IsSymmetric f)
    (hV : 2 ≤ Fintype.card V) {vs : List V} (hcov : ∀ v, v ∈ vs) :
    let res := (queyranneQuery vs).eval (ValueQuery.oracleOf f)
    IsNonTrivialCut res.cut ∧ res.val = f res.cut ∧
      ∀ C : Finset V, IsNonTrivialCut C → f res.cut ≤ f C := by
  rw [eval_queyranneQuery_oracleOf]
  exact queyranne_spec hf hsym hV hcov

end OracleMinimization

end Cslib.Query
