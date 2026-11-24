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
   `countQueries_queyranneQuery_le_card_cubed`, `queyranneQuery_upperBound`): for `2 ≤ n`,
   `3 * Q ≤ n³` (hence `Q ≤ n³ ≤ vs.length³`), giving `UpperBound queyranneQuery List.length
   (fun n => n ^ 3 + 1)` unconditionally over all `List V`.
3. **End-to-end oracle optimality**: `eval_queyranneQuery_spec` combines `queyranne_spec` with
   `eval_queyranneQuery_oracleOf` for symmetric submodular functions accessed via value queries.

Note: Primary PDF locators for `[Queyranne1998]` were not inspected against a local PDF.

## Main definitions

* `Cslib.Query.queyranneQuery`: Queyranne's minimization algorithm in `FreeM (ValueQuery V β)`.

## Main results

* `eval_queyranneQuery`, `eval_queyranneQuery_oracleOf`: agreement with pure `queyranne`.
* `countQueries_queyranneQuery_eq`, `three_mul_countQueries_queyranneQuery_le`,
  `countQueries_queyranneQuery_le_card_cubed`, `countQueries_queyranneQuery_le`,
  `queyranneQuery_upperBound`: exact query count and `O(|V|³)` upper bound.
* `eval_queyranneQuery_spec`: global symmetric submodular minimization guarantee via value oracle.

## References

* [Queyranne1998] Maurice Queyranne,
  *Minimizing symmetric submodular functions*, *Mathematical Programming* **82** (1998), 3–12.
-/

public section

open Cslib.Algorithms.Lean.Submodular
open Cslib.WeightedCut (IsNonTrivialCut)

namespace Cslib.Query

/-- Value-oracle query tree for Queyranne's symmetric submodular minimization algorithm. -/
@[expose] def queyranneQuery {V β : Type} [DecidableEq V] [Add β] [LT β] [DecidableLT β]
    (vs : List V) : FreeM (ValueQuery V β) (Finset V × β) :=
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

private theorem nodup_of_disj {blocks : List (Finset V)}
    (hne : ∀ b ∈ blocks, b.Nonempty) (hdisj : blocks.Pairwise Disjoint) :
    blocks.Nodup := by
  induction blocks with
  | nil => exact List.nodup_nil
  | cons b bs ih =>
    obtain ⟨hpair, hrest⟩ := List.pairwise_cons.mp hdisj
    refine List.nodup_cons.mpr ⟨fun hb => ?_, ih (fun c hc => hne c (List.mem_cons_of_mem b hc))
      hrest⟩
    obtain ⟨x, hx⟩ := hne b List.mem_cons_self
    exact Finset.disjoint_left.mp (hpair b hb) hx hx

section EraseBlock

variable [DecidableEq V]

private theorem length_eraseBlock_of_mem {p : Finset V} :
    ∀ {cs : List (Finset V × β)}, (∃ sb, (p, sb) ∈ cs) →
      (eraseBlock p cs).length + 1 = cs.length
  | [], ⟨_, h⟩ => by simp at h
  | (b, sb) :: cs, ⟨sb', h⟩ => by
    rw [eraseBlock]
    by_cases hbp : b = p
    · simp [hbp]
    · simp only [hbp, ↓reduceIte, List.length_cons]
      have h' : ∃ sb, (p, sb) ∈ cs := by
        rcases List.mem_cons.mp h with heq | hc
        · exact absurd (Prod.mk.inj heq).1.symm hbp
        · exact ⟨sb', hc⟩
      have ih := length_eraseBlock_of_mem h'
      omega

private theorem mem_eraseBlock_iff_of_nodup {p : Finset V} :
    ∀ {cs : List (Finset V × β)}, (cs.map Prod.fst).Nodup →
      ∀ {c : Finset V × β}, c ∈ eraseBlock p cs ↔ c ∈ cs ∧ c.1 ≠ p
  | [], _, _ => by simp [eraseBlock]
  | (b, sb) :: cs, hnd, (x, sx) => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [eraseBlock]
    by_cases hbp : b = p
    · subst hbp
      simp only [↓reduceIte, List.mem_cons, Prod.mk.injEq, ne_eq]
      constructor
      · intro hx
        refine ⟨.inr hx, fun hxp => ?_⟩
        subst hxp
        exact hnd.1 (List.mem_map.mpr ⟨(x, sx), hx, rfl⟩)
      · rintro ⟨⟨rfl, rfl⟩ | hx, hne⟩
        · exact absurd rfl hne
        · exact hx
    · simp only [hbp, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ne_eq]
      rw [mem_eraseBlock_iff_of_nodup hnd.2]
      refine ⟨?_, ?_⟩
      · rintro (⟨rfl, rfl⟩ | ⟨hx, hne⟩)
        · exact ⟨.inl ⟨rfl, rfl⟩, hbp⟩
        · exact ⟨.inr hx, hne⟩
      · rintro ⟨⟨rfl, rfl⟩ | hx, hne⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨hx, hne⟩

private theorem nodup_fst_eraseBlock_of_nodup (p : Finset V)
    {cs : List (Finset V × β)} (hnd : (cs.map Prod.fst).Nodup) :
    ((eraseBlock p cs).map Prod.fst).Nodup := by
  induction cs with
  | nil => simp [eraseBlock]
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [eraseBlock]
    by_cases hbp : b = p
    · simpa [hbp] using hnd.2
    · simp only [hbp, ↓reduceIte, List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih hnd.2⟩
      obtain ⟨⟨x, sx⟩, hx, rfl⟩ := List.mem_map.mp hmem
      exact hnd.1
        (List.mem_map.mpr ⟨(x, sx), ((mem_eraseBlock_iff_of_nodup hnd.2).mp hx).1, rfl⟩)

private theorem disj_mergeBlocks {blocks : List (Finset V)}
    (hne : ∀ b ∈ blocks, b.Nonempty) (hdisj : blocks.Pairwise Disjoint)
    {s t : Finset V} (hs : s ∈ blocks) (ht : t ∈ blocks) (hst : s ≠ t) :
    (∀ b ∈ mergeBlocks s t blocks, b.Nonempty) ∧ (mergeBlocks s t blocks).Pairwise Disjoint := by
  have hnd := nodup_of_disj hne hdisj
  have hsub : ∀ b ∈ (blocks.erase s).erase t, b ∈ blocks ∧ b ≠ s ∧ b ≠ t := by
    intro b hb
    have hb1 : b ∈ blocks.erase s := List.mem_of_mem_erase hb
    have hb0 : b ∈ blocks := List.mem_of_mem_erase hb1
    have hbt : b ≠ t := fun h => by
      subst h
      exact (hnd.erase s).not_mem_erase hb
    have hbs : b ≠ s := fun h => by
      subst h
      exact hnd.not_mem_erase hb1
    exact ⟨hb0, hbs, hbt⟩
  refine ⟨?_, List.pairwise_cons.mpr ⟨?_, (hdisj.sublist List.erase_sublist).sublist
    List.erase_sublist⟩⟩
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact (hne s hs).mono Finset.subset_union_left
    · exact hne b (hsub b hb').1
  · intro b hb
    obtain ⟨hb0, hbs, hbt⟩ := hsub b hb
    exact Finset.disjoint_union_left.mpr
      ⟨hdisj.forall hs hb0 hbs.symm, hdisj.forall ht hb0 hbt.symm⟩

private theorem length_mergeBlocks_of_mem {blocks : List (Finset V)} {s t : Finset V}
    (hs : s ∈ blocks) (ht : t ∈ blocks) (hst : s ≠ t) :
    (mergeBlocks s t blocks).length + 1 = blocks.length := by
  have ht' : t ∈ blocks.erase s := (List.mem_erase_of_ne hst.symm).mpr ht
  have hpos : 0 < (blocks.erase s).length := List.length_pos_of_mem ht'
  have h1 := List.length_erase_of_mem ht'
  have h2 := List.length_erase_of_mem hs
  rw [h2] at hpos
  simp only [mergeBlocks, List.length_cons, h1, h2]
  omega

end EraseBlock

variable [DecidableEq V] [Add β] [LT β] [DecidableLT β]

/-- Evaluating `queyranneQuery` against `oracle` agrees with `queyranne` on
`fun S => oracle (.value S)`. -/
@[simp] theorem eval_queyranneQuery
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (vs : List V) :
    (queyranneQuery vs).eval oracle = queyranne (fun S => oracle (.value S)) vs :=
  Id.pure_injective <| by
    simp [queyranneQuery, queyranne,
      FreeM.isMonadHom_pure_eval oracle |>.map_queyranneM _ vs]

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

private theorem eval_qScanM_fst_mem
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (A best : Finset V) (sBest vBest : β) (cs : List (Finset V × β)) :
    ∃ sb, (((qScanM ValueQuery.ask A best sBest vBest cs).eval oracle).1, sb) ∈
      (best, sBest) :: cs := by
  induction cs generalizing best sBest vBest with
  | nil => exact ⟨sBest, List.mem_cons_self⟩
  | cons c cs ih =>
    rcases c with ⟨b, sb⟩
    simp only [qScanM, FreeM.eval_bind, ValueQuery.eval_ask]
    by_cases h : oracle (.value (A ∪ b)) + sBest < vBest + sb
    · simp only [h, ↓reduceIte]
      obtain ⟨s, hs⟩ := ih b sb (oracle (.value (A ∪ b)))
      exact ⟨s, List.mem_cons_of_mem _ hs⟩
    · simp only [h, ↓reduceIte]
      obtain ⟨s, hs⟩ := ih best sBest vBest
      rcases List.mem_cons.mp hs with heq | hmem
      · exact ⟨s, heq ▸ List.mem_cons_self⟩
      · exact ⟨s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)⟩

private theorem countQueries_qSearchStepsM_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι) :
    ∀ (k : ℕ) (A prev : Finset V) (c₀ : Finset V × β) (cs : List (Finset V × β)),
      cs.length = k →
      2 * (qSearchStepsM ValueQuery.ask k A prev c₀ cs).countQueries oracle = k * (k + 3)
  | 0, _, prev, (t, st), _, _ => by simp [qSearchStepsM]
  | _ + 1, _, prev, (t, st), [], hlen => by simp at hlen
  | k + 1, A, prev, c₀, c₁ :: cs, hlen => by
    have hscan_mem :=
      eval_qScanM_fst_mem oracle A c₀.1 c₀.2 (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)
    set best := ((qScanM ValueQuery.ask A c₀.1 c₀.2
      (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).1
    have hlen_er := length_eraseBlock_of_mem hscan_mem
    simp only [qSearchStepsM, FreeM.countQueries_bind, ValueQuery.countQueries_ask,
      ValueQuery.eval_ask, countQueries_qScanM]
    cases her : eraseBlock best (c₀ :: c₁ :: cs) with
    | nil =>
      rw [her, List.length_nil] at hlen_er
      simp at hlen_er
    | cons d₀ ds =>
      have hds_len : ds.length = k := by
        simp only [her, List.length_cons] at hlen hlen_er
        omega
      have ih := countQueries_qSearchStepsM_eq oracle k (A ∪ best) best d₀ ds hds_len
      have hcs_len : (c₁ :: cs).length = k + 1 := hlen
      rw [hcs_len]
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
      res.1 ∈ blocks ∧ res.2.1 ∈ blocks ∧ res.1 ≠ res.2.1
  | 0, _, prev, (t, st), _, _, hprev, hmem, _, hnot => by
    have ht : t ∈ blocks := hmem (t, st) List.mem_cons_self
    have hne : prev ≠ t := fun h => hnot (by simp [h])
    simpa [qSearchStepsM] using ⟨hprev, ht, hne⟩
  | _ + 1, _, prev, (t, st), [], hlen, _, _, _, _ => by simp at hlen
  | k + 1, A, prev, c₀, c₁ :: cs, hlen, _, hmem, hnd, _ => by
    have hscan_mem :=
      eval_qScanM_fst_mem oracle A c₀.1 c₀.2 (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)
    set best := ((qScanM ValueQuery.ask A c₀.1 c₀.2
      (oracle (.value (A ∪ c₀.1))) (c₁ :: cs)).eval oracle).1
    obtain ⟨sBest, hsBest⟩ := hscan_mem
    have hbest_mem : best ∈ blocks := hmem (best, sBest) hsBest
    have hlen_er := length_eraseBlock_of_mem ⟨sBest, hsBest⟩
    cases her : eraseBlock best (c₀ :: c₁ :: cs) with
    | nil =>
      rw [her, List.length_nil] at hlen_er
      simp at hlen_er
    | cons d₀ ds =>
      have hds_len : ds.length = k := by
        simp only [her, List.length_cons] at hlen hlen_er
        omega
      have hnd' : ((d₀ :: ds).map Prod.fst).Nodup :=
        her ▸ nodup_fst_eraseBlock_of_nodup best hnd
      have hsub' : ∀ p ∈ d₀ :: ds, p ∈ c₀ :: c₁ :: cs ∧ p.1 ≠ best := by
        intro p hp'
        rw [← her] at hp'
        exact (mem_eraseBlock_iff_of_nodup hnd).mp hp'
      have hmem' : ∀ p ∈ d₀ :: ds, p.1 ∈ blocks := fun p hp' => hmem p (hsub' p hp').1
      have hnot' : best ∉ (d₀ :: ds).map Prod.fst := by
        intro hin
        obtain ⟨p, hp', hpeq⟩ := List.mem_map.mp hin
        exact (hsub' p hp').2 hpeq
      have ih := eval_qSearchStepsM_spec oracle k (A ∪ best) best d₀ ds hds_len
        hbest_mem hmem' hnd' hnot'
      simpa [qSearchStepsM, her, best] using ih

private theorem countQueries_qSearchM_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    (b₀ b₁ : Finset V) (bs : List (Finset V)) :
    2 * (qSearchM ValueQuery.ask b₀ b₁ bs).countQueries oracle + 4 =
      (bs.length + 2) * (bs.length + 3) := by
  simp only [qSearchM, FreeM.countQueries_bind, countQueries_qSingletonsM, List.length_cons]
  cases hc : (qSingletonsM (ValueQuery.ask (α := V) (β := β)) (b₁ :: bs)).eval oracle with
  | nil =>
    have hlen := map_fst_eval_qSingletonsM oracle (b₁ :: bs)
    rw [hc] at hlen
    simp at hlen
  | cons c₀ cs =>
    have hmap := map_fst_eval_qSingletonsM oracle (b₁ :: bs)
    rw [hc] at hmap
    have hlen : cs.length = bs.length := by
      have hl := congrArg List.length hmap
      simp only [List.length_map, List.length_cons] at hl
      omega
    have hsteps := countQueries_qSearchStepsM_eq oracle bs.length b₀ b₀ c₀ cs hlen
    dsimp only
    nlinarith

private theorem eval_qSearchM_mem
    (oracle : {ι : Type} → ValueQuery V β ι → ι)
    {b₀ b₁ : Finset V} {bs : List (Finset V)} (hnd : (b₀ :: b₁ :: bs).Nodup) :
    let res := (qSearchM ValueQuery.ask b₀ b₁ bs).eval oracle
    res.1 ∈ b₀ :: b₁ :: bs ∧ res.2.1 ∈ b₀ :: b₁ :: bs ∧ res.1 ≠ res.2.1 := by
  simp only [qSearchM, FreeM.eval_bind]
  have hmap := map_fst_eval_qSingletonsM oracle (b₁ :: bs)
  cases hc : (qSingletonsM (ValueQuery.ask (α := V) (β := β)) (b₁ :: bs)).eval oracle with
  | nil =>
    rw [hc] at hmap
    simp at hmap
  | cons c₀ cs =>
    rw [hc] at hmap
    have hlen : cs.length = bs.length := by
      have hl := congrArg List.length hmap
      simp only [List.length_map, List.length_cons] at hl
      omega
    rw [List.nodup_cons] at hnd
    have hc_mem : ∀ p ∈ c₀ :: cs, p.1 ∈ b₀ :: b₁ :: bs := by
      intro p hp
      have hp' : p.1 ∈ (c₀ :: cs).map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [hmap] at hp'
      exact List.mem_cons_of_mem b₀ hp'
    have hc_nd : ((c₀ :: cs).map Prod.fst).Nodup := hmap ▸ hnd.2
    have hc_not : b₀ ∉ (c₀ :: cs).map Prod.fst := hmap ▸ hnd.1
    exact eval_qSearchStepsM_spec oracle bs.length b₀ b₀ c₀ cs hlen
      List.mem_cons_self hc_mem hc_nd hc_not

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
    rcases blocks with _ | ⟨b₀, _ | ⟨b₁, bs⟩⟩
    · simp at hlen
    · simp at hlen
    · have hnd := nodup_of_disj hne hdisj
      have hsearch := eval_qSearchM_mem oracle hnd
      set sr := (qSearchM ValueQuery.ask b₀ b₁ bs).eval oracle
      have hmerge := disj_mergeBlocks hne hdisj hsearch.1 hsearch.2.1 hsearch.2.2
      have hlen' : (mergeBlocks sr.1 sr.2.1 (b₀ :: b₁ :: bs)).length = steps + 2 := by
        have hm := length_mergeBlocks_of_mem hsearch.1 hsearch.2.1 hsearch.2.2
        omega
      have ih := countQueries_queyranneRecM_eq oracle steps
        (mergeBlocks sr.1 sr.2.1 (b₀ :: b₁ :: bs)) hmerge.1 hmerge.2 hlen'
      have hq := countQueries_qSearchM_eq oracle b₀ b₁ bs
      have hbs_len1 : bs.length + 2 = steps + 3 := by
        simp only [List.length_cons] at hlen
        omega
      have hbs_len2 : bs.length + 3 = steps + 4 := by omega
      rw [hbs_len1, hbs_len2] at hq
      simp only [queyranneRecM, FreeM.countQueries_bind]
      set qrec := (queyranneRecM ValueQuery.ask steps
        (mergeBlocks sr.1 sr.2.1 (b₀ :: b₁ :: bs))).countQueries oracle
      set qs := (qSearchM ValueQuery.ask b₀ b₁ bs).countQueries oracle
      set recRes := (queyranneRecM ValueQuery.ask steps
        (mergeBlocks sr.1 sr.2.1 (b₀ :: b₁ :: bs))).eval oracle
      have htail :
          FreeM.countQueries oracle
            (if recRes.2 < sr.2.2 then
              (pure (recRes.1, recRes.2) : FreeM (ValueQuery V β) (Finset V × β))
            else
              pure (sr.2.1, sr.2.2)) = 0 := by
        split_ifs <;> simp
      change 6 * (qs + (qrec + _)) + 12 * (steps + 1 + 2) = _
      rw [htail]
      linarith

/-- **Exact value-oracle query complexity** ([Queyranne1998]): when `2 ≤ n := vs.toFinset.card`,
against any value oracle `queyranneQuery vs` performs `Q` queries satisfying
`6 * Q + 12 * n = n * (n + 1) * (n + 2) + 6`. -/
theorem countQueries_queyranneQuery_eq
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : 2 ≤ vs.toFinset.card) :
    6 * (queyranneQuery vs).countQueries oracle + 12 * vs.toFinset.card =
      vs.toFinset.card * (vs.toFinset.card + 1) * (vs.toFinset.card + 2) + 6 := by
  have hu_nd : vs.eraseDups.Nodup := List.nodup_eraseDups vs
  have hu_len : vs.eraseDups.length = vs.toFinset.card := List.length_eraseDups vs
  have hne : ∀ b ∈ vs.eraseDups.map ({·} : V → Finset V), b.Nonempty := by
    intro b hb
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    exact Finset.singleton_nonempty v
  have hdisj : (vs.eraseDups.map ({·} : V → Finset V)).Pairwise Disjoint :=
    List.pairwise_map.mpr (hu_nd.imp fun hab => Finset.disjoint_singleton.mpr hab)
  have hlen : (vs.eraseDups.map ({·} : V → Finset V)).length =
      (vs.eraseDups.length - 2) + 2 := by
    rw [List.length_map]
    omega
  have hrec := countQueries_queyranneRecM_eq oracle (vs.eraseDups.length - 2) _ hne hdisj hlen
  have h1 : vs.eraseDups.length - 2 + 2 = vs.toFinset.card := by omega
  have h2 : vs.eraseDups.length - 2 + 3 = vs.toFinset.card + 1 := by omega
  have h3 : vs.eraseDups.length - 2 + 4 = vs.toFinset.card + 2 := by omega
  rw [h1, h2, h3] at hrec
  exact hrec

/-- On degenerate inputs with fewer than two distinct elements, `queyranneQuery vs` makes `1`
query (`∅`). -/
theorem countQueries_queyranneQuery_eq_one_of_lt_two
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : vs.toFinset.card < 2) :
    (queyranneQuery vs).countQueries oracle = 1 := by
  have hu_len : vs.eraseDups.length = vs.toFinset.card := List.length_eraseDups vs
  have hlen : vs.eraseDups.length < 2 := hu_len.symm ▸ hvs
  simp only [queyranneQuery, queyranneM]
  cases hu : vs.eraseDups with
  | nil => simp [queyranneRecM]
  | cons a rest =>
    cases hrest : rest with
    | nil => simp [queyranneRecM]
    | cons b bs =>
      rw [hu, hrest] at hlen
      simp at hlen

/-- When `2 ≤ vs.toFinset.card`, `3 * countQueries ≤ vs.toFinset.card ^ 3` against any oracle. -/
theorem three_mul_countQueries_queyranneQuery_le
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : 2 ≤ vs.toFinset.card) :
    3 * (queyranneQuery vs).countQueries oracle ≤ vs.toFinset.card ^ 3 := by
  have heq := countQueries_queyranneQuery_eq oracle hvs
  set n := vs.toFinset.card
  rcases Nat.eq_or_lt_of_le hvs with heq2 | hn
  · rw [← heq2] at heq ⊢
    omega
  · have hge3 : 3 ≤ n := hn
    nlinarith

/-- For `2 ≤ vs.toFinset.card`, `queyranneQuery vs` makes at most `vs.toFinset.card ^ 3` value
queries against any oracle. -/
theorem countQueries_queyranneQuery_le_card_cubed
    (oracle : {ι : Type} → ValueQuery V β ι → ι) {vs : List V} (hvs : 2 ≤ vs.toFinset.card) :
    (queyranneQuery vs).countQueries oracle ≤ vs.toFinset.card ^ 3 :=
  (Nat.le_mul_of_pos_left _ (by omega)).trans (three_mul_countQueries_queyranneQuery_le oracle hvs)

/-- Pointwise cubic upper bound valid for all input lists `vs`, including degenerate lists with
`vs.toFinset.card < 2`. -/
theorem countQueries_queyranneQuery_le
    (oracle : {ι : Type} → ValueQuery V β ι → ι) (vs : List V) :
    (queyranneQuery vs).countQueries oracle ≤ vs.length ^ 3 + 1 := by
  by_cases hvs : 2 ≤ vs.toFinset.card
  · exact ((countQueries_queyranneQuery_le_card_cubed oracle hvs).trans
      (Nat.pow_le_pow_left (List.toFinset_card_le vs) 3)).trans (Nat.le_succ _)
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
    IsNonTrivialCut res.1 ∧ res.2 = f res.1 ∧
      ∀ C : Finset V, IsNonTrivialCut C → f res.1 ≤ f C := by
  rw [eval_queyranneQuery_oracleOf]
  exact queyranne_spec hf hsym hV hcov

end OracleMinimization

end Cslib.Query
