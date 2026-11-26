/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Paging.Basic
import Mathlib.Data.List.FinRange

/-!
# Deterministic `k`-competitive lower bound for online paging

This file formalizes Theorem 5 of
[Sleator and Tarjan, *Amortized Efficiency of List Update and Paging Rules*, Section 4 ("Paging"),
p. 207][SleatorTarjan1985] at equal online and offline fast-memory capacity (`n_A = n_MIN = k`,
`0 < k`): no deterministic online paging strategy can achieve a competitive ratio strictly smaller
than `k` (neither any rational ratio `p / q < k` via `exists_ratio_violation_of_lt`, nor any
integer factor `c < k` via `not_isCompetitiveFrom_of_lt`), regardless of the additive constant
`b : Nat` and even when restricted to starting from the empty cache `∅`.

## Source statement and proof structure

In [SleatorTarjan1985], Section 4 ("Paging"), p. 207, Theorem 5 shows for fast-memory capacities
`n_MIN ≤ n_A` that against a universe of `n_A + 1` pages, for any deterministic online paging
algorithm `A` there exist arbitrarily long request sequences on which `A` incurs at least
`n_A / (n_A - n_MIN + 1)` times as many faults (up to initial-cache warmup) as an offline algorithm
of capacity `n_MIN`. Specializing to `n_A = n_MIN = k`:

1. **Explicit computable adversary (`missingPage`, `adversaryRequests`):** Given `k + 1` distinct
   pages `pages : List α` (`pages.Nodup`, `pages.length = k + 1`), `A`'s current cache `s` holds at
   most `k` pages, so `missingPage` computably selects the first page of `pages` absent from `s`.
   Stepping `DetStrategy.adaptiveRequests` for `n` steps produces a concrete request list `reqs` of
   length `n` drawn from `pages` on which `A` faults at every single step (`A.cost s₀ reqs = n`).
2. **Computable offline lookahead schedule (`offlineLookahead`):** On any request sequence drawn
   from `pages`, whenever the offline cache `s` (`s.card = k`, `s ⊆ pages.toFinset`) misses a
   page `p`, `insert p s = pages.toFinset` covers the entire `(k + 1)`-page universe. Lookahead
   over `window := (rest.take (k - 1)).toFinset` (`window.card ≤ k - 1 < k`) computably selects a
   resident page `evict ∈ s \ window` to evict. Because `s' = pages.toFinset.erase evict` contains
   every page in `pages` other than `evict`, the offline schedule serves the next `k - 1` requests
   with zero faults, establishing
   `k * optCost ≤ reqs.length + (k - 1) * (k - s₀.card) + (k - 1)`.
3. **Impossibility for any ratio `p / q < k` (`p < k * q`) and integer `c < k`:** Setting
   `n = k * (p * k + b + 1)` forces `A.cost s₀ reqs = n` while `p * optCost + b < q * n`
   (`exists_ratio_violation_of_lt`), refuting every rational competitive ratio `< k` (including
   ratios `< 1` at `k = 1`). Specializing to `q = 1, p = c` refutes `IsCompetitiveFrom s₀ c b`
   (including `s₀ = ∅`), `IsCompetitive c b`, and `IsCompetitiveAnyInit c b`. Specializing `pages`
   to `List.finRange (k + 1)` gives parameter-free corollaries on `Fin (k + 1)`.

## Main definitions

* `Cslib.DataStructure.Paging.missingPage`: computable selection of a page in `pages` outside `s`.
* `Cslib.DataStructure.Paging.adversaryRequests`: explicit length-`n` adversarial request sequence
  against a deterministic online paging strategy.
* `Cslib.DataStructure.Paging.offlineLookahead`: computable `(k - 1)`-step lookahead offline
  schedule over a `(k + 1)`-page universe.

## Main results

* `cost_adversaryRequests`: `A` faults on every request of `adversaryRequests` (`cost = n`).
* `validSchedule_offlineLookahead`, `scheduleCost_offlineLookahead_bound`: `offlineLookahead` is a
  valid demand-paging schedule faulting at most once per `k` requests after warmup.
* `exists_witness_of_card_eq`: from a full cache (`s₀.card = k`), `A` incurs `k * m` faults while
  `offlineLookahead` incurs at most `m` faults.
* `exists_ratio_violation_of_lt`, `fin_exists_ratio_violation_empty_of_lt`: no deterministic online
  paging strategy over `≥ k + 1` pages achieves any rational competitive ratio `p / q < k`
  (`p < k * q`) with any additive constant `b`.
* `not_isCompetitiveFrom_of_lt`, `not_isCompetitive_of_lt`, `not_isCompetitiveAnyInit_of_lt`:
  integer-factor specializations refuting `(c, b)`-competitiveness for `c < k`.
* `fin_not_isCompetitiveFrom_empty_of_lt`, `fin_not_isCompetitive_of_lt`,
  `fin_not_isCompetitiveAnyInit_of_lt`: canonical lower bounds on `Fin (k + 1)`.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Paging

open Cslib.DataStructure.Online

variable {α : Type} [DecidableEq α]

/-! ### Computable pigeonhole page selection and adversarial requests -/

/-- Return the first element of `pages` not belonging to `s`, falling back to `p₀` if none exists.
When `pages.Nodup` and `s.card < pages.length`, the fallback is never reached. -/
@[expose]
def missingPage (p₀ : α) : List α → Finset α → α
  | [], _ => p₀
  | x :: xs, s => if x ∈ s then missingPage p₀ xs s else x

private theorem missingPage_erase_of_notMem (p₀ : α) {x : α} {xs : List α} (hx : x ∉ xs)
    (s : Finset α) :
    missingPage p₀ xs (s.erase x) = missingPage p₀ xs s := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hyx : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    have hmem : (y ∈ s.erase x) ↔ (y ∈ s) := Finset.mem_erase.trans (and_iff_right hyx)
    simp only [missingPage, hmem, ih (fun h => hx (List.mem_cons_of_mem y h))]

/-- Pigeonhole selection: if `pages` is duplicate-free and `s` has strictly fewer elements than
`pages`, then `missingPage p₀ pages s` belongs to `pages` and lies outside `s`. -/
theorem missingPage_mem_and_notMem (p₀ : α) {pages : List α} {s : Finset α}
    (hnodup : pages.Nodup) (hcard : s.card < pages.length) :
    missingPage p₀ pages s ∈ pages ∧ missingPage p₀ pages s ∉ s := by
  induction pages generalizing s with
  | nil => cases hcard
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hx_xs, hnodup'⟩
    simp only [missingPage]
    split
    · next hxs =>
      rw [← Finset.card_erase_add_one hxs, List.length_cons] at hcard
      obtain ⟨hmem, hnot⟩ := ih hnodup' (Nat.lt_of_succ_lt_succ hcard)
      rw [missingPage_erase_of_notMem p₀ hx_xs s] at hmem hnot
      have hne : missingPage p₀ xs s ≠ x := fun h => hx_xs (h ▸ hmem)
      refine ⟨List.mem_cons_of_mem x hmem, fun hs => hnot (Finset.mem_erase.mpr ⟨hne, hs⟩)⟩
    · next hxs =>
      exact ⟨List.mem_cons_self, hxs⟩

/-- Explicit adversarial request sequence of length `n` generated against deterministic online
paging strategy `A` from initial cache `s₀`, repeatedly requesting `missingPage p₀ pages` on `A`'s
current cache. -/
@[expose]
def adversaryRequests {k : Nat} (p₀ : α) (pages : List α) (A : DetStrategy (problem α k))
    (s₀ : Finset α) (n : Nat) : List α :=
  A.adaptiveRequests (missingPage p₀ pages) s₀ n

@[simp]
theorem adversaryRequests_length {k : Nat} (p₀ : α) (pages : List α)
    (A : DetStrategy (problem α k)) (s₀ : Finset α) (n : Nat) :
    (adversaryRequests p₀ pages A s₀ n).length = n :=
  A.adaptiveRequests_length (missingPage p₀ pages) s₀ n

/-- Every request in `adversaryRequests` belongs to `pages` when `pages.Nodup`,
`pages.length = k + 1`, and `s₀.card ≤ k`. -/
theorem mem_adversaryRequests {k : Nat} (p₀ : α) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    (A : DetStrategy (problem α k)) {s₀ : Finset α} (hs₀ : ValidCache k s₀)
    {n : Nat} {r : α} (hr : r ∈ adversaryRequests p₀ pages A s₀ n) :
    r ∈ pages := by
  apply A.mem_adaptiveRequests (Q := fun p => p ∈ pages) _ hs₀ hr
  intro m hm
  have hcard : (A.project m).card ≤ k := (A.valid_step p₀ hm).2.1
  exact (missingPage_mem_and_notMem p₀ hnodup (by omega)).1

/-- Any deterministic online strategy `A` faults on every single request of `adversaryRequests`,
incurring exact cost `n`. -/
theorem cost_adversaryRequests {k : Nat} (p₀ : α) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    (A : DetStrategy (problem α k)) {s₀ : Finset α} (hs₀ : ValidCache k s₀) (n : Nat) :
    A.cost s₀ (adversaryRequests p₀ pages A s₀ n) = n := by
  simpa only [adversaryRequests, Nat.mul_one] using
    A.cost_adaptiveRequests_eq (chooseReq := missingPage p₀ pages) (w := 1)
      (fun {m} hm => stepCost_of_notMem
        (s' := A.project (A.step m (missingPage p₀ pages (A.project m))))
        (missingPage_mem_and_notMem p₀ hnodup
          (by have := (A.valid_step p₀ hm).2.1; omega)).2) hs₀ n

/-! ### Computable `(k - 1)`-lookahead offline schedule over `k + 1` pages -/

/-- Structural helper for `offlineLookahead`: when `skip = n + 1`, holds `s` across the next warm
request before resuming lookahead at `skip = 0`. -/
@[expose]
def offlineLookaheadAux (k : Nat) (p₀ : α) (pages : List α) :
    Nat → Finset α → List α → List (Finset α)
  | _, _, [] => []
  | skip + 1, s, _ :: rest => s :: offlineLookaheadAux k p₀ pages skip s rest
  | 0, s, p :: rest =>
    if p ∈ s then
      s :: offlineLookaheadAux k p₀ pages 0 s rest
    else if s.card < k then
      let s' := insert p s
      s' :: offlineLookaheadAux k p₀ pages 0 s' rest
    else
      let window := (rest.take (k - 1)).toFinset
      let evict := missingPage p₀ (pages.filter (· ∈ s)) window
      let s' := insert p (s.erase evict)
      s' :: offlineLookaheadAux k p₀ pages (k - 1) s' rest

/-- Computable offline schedule over a `(k + 1)`-page universe `pages`: hits keep `s` unchanged,
misses when `s.card < k` insert `p`, and misses when `s.card = k` evict a cached page absent from
the next `k - 1` requests and hold the resulting cache across those `k - 1` requests. -/
@[expose]
def offlineLookahead (k : Nat) (p₀ : α) (pages : List α) (s : Finset α) (reqs : List α) :
    List (Finset α) :=
  offlineLookaheadAux k p₀ pages 0 s reqs

private theorem offlineLookaheadAux_eq_replicate_append (k : Nat) (p₀ : α) (pages : List α) :
    ∀ (skip : Nat) (s : Finset α) (reqs : List α),
      offlineLookaheadAux k p₀ pages skip s reqs =
        List.replicate (reqs.take skip).length s ++
          offlineLookahead k p₀ pages s (reqs.drop skip)
  | 0, _, _ => by simp [offlineLookahead]
  | _ + 1, _, [] => rfl
  | skip + 1, s, _ :: rest => by
    simp only [offlineLookaheadAux, List.take_succ_cons, List.length_cons, List.replicate_succ,
      List.cons_append, List.drop_succ_cons,
      offlineLookaheadAux_eq_replicate_append k p₀ pages skip]

@[simp]
theorem offlineLookahead_nil (k : Nat) (p₀ : α) (pages : List α) (s : Finset α) :
    offlineLookahead k p₀ pages s [] = [] := rfl

theorem offlineLookahead_cons (k : Nat) (p₀ : α) (pages : List α) (s : Finset α)
    (p : α) (rest : List α) :
    offlineLookahead k p₀ pages s (p :: rest) =
      if p ∈ s then
        s :: offlineLookahead k p₀ pages s rest
      else if s.card < k then
        let s' := insert p s
        s' :: offlineLookahead k p₀ pages s' rest
      else
        let window := (rest.take (k - 1)).toFinset
        let evict := missingPage p₀ (pages.filter (· ∈ s)) window
        let s' := insert p (s.erase evict)
        s' :: (List.replicate (rest.take (k - 1)).length s' ++
          offlineLookahead k p₀ pages s' (rest.drop (k - 1))) := by
  rw [offlineLookahead, offlineLookaheadAux]
  split_ifs
  exacts [rfl, rfl, congrArg _ (offlineLookaheadAux_eq_replicate_append _ _ _ _ _ _)]

private theorem filter_mem_length_eq_card {pages : List α} {s : Finset α}
    (hnodup : pages.Nodup) (hsub : s ⊆ pages.toFinset) :
    (pages.filter (· ∈ s)).length = s.card := by
  rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
  congr 1
  ext x
  simpa [List.mem_toFinset] using fun hx => List.mem_toFinset.mp (hsub hx)

private theorem evict_mem_and_notMem {k : Nat} (p₀ : α) {pages : List α} {s : Finset α}
    (hnodup : pages.Nodup) (hsub : s ⊆ pages.toFinset) (hscard : s.card = k)
    (rest : List α) (hk : 0 < k) :
    let window := (rest.take (k - 1)).toFinset
    let evict := missingPage p₀ (pages.filter (· ∈ s)) window
    evict ∈ s ∧ evict ∉ window := by
  dsimp only
  have hwcard : (rest.take (k - 1)).toFinset.card < (pages.filter (· ∈ s)).length := by
    have := (List.toFinset_card_le (rest.take (k - 1))).trans (List.length_take_le _ _)
    have := (filter_mem_length_eq_card hnodup hsub).trans hscard
    omega
  obtain ⟨hmem, hnot⟩ := missingPage_mem_and_notMem p₀ (hnodup.filter _) hwcard
  exact ⟨of_decide_eq_true (List.mem_filter.mp hmem).2, hnot⟩

private theorem warm_mem_next_cache {k : Nat} {pages rest : List α} {s : Finset α} {p evict : α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    (hsub : s ⊆ pages.toFinset) (hscard : s.card = k)
    (hp_pages : p ∈ pages) (hp_not : p ∉ s)
    (hnot_win : evict ∉ (List.take (k - 1) rest).toFinset)
    (hrest_pages : ∀ r ∈ rest, r ∈ pages) :
    ∀ q ∈ rest.take (k - 1), q ∈ insert p (s.erase evict) := by
  have hins_eq : insert p s = pages.toFinset :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset (List.mem_toFinset.mpr hp_pages) hsub)
      (by rw [List.toFinset_card_of_nodup hnodup, hlen, Finset.card_insert_of_notMem hp_not,
        hscard])
  intro q hq
  have hq_pages : q ∈ insert p s :=
    hins_eq.symm ▸ List.mem_toFinset.mpr (hrest_pages q (List.mem_of_mem_take hq))
  have hq_ne : q ≠ evict := fun h => hnot_win (h ▸ List.mem_toFinset.mpr hq)
  rcases Finset.mem_insert.mp hq_pages with rfl | hqs
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hq_ne, hqs⟩)

/-- `offlineLookahead` produces a valid demand-paging schedule whenever `0 < k`, `s` is a valid
subset of `pages`, and all requests come from `pages`. -/
theorem validSchedule_offlineLookahead {k : Nat} (hk : 0 < k) (p₀ : α) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1) :
    ∀ {s : Finset α} (reqs : List α),
      s.card ≤ k →
      s ⊆ pages.toFinset →
      (∀ r ∈ reqs, r ∈ pages) →
      (problem α k).ValidSchedule s reqs (offlineLookahead k p₀ pages s reqs)
  | s, [], _, _, _ => trivial
  | s, p :: rest, hscard, hsub, hreqs => by
    have hp_pages : p ∈ pages := hreqs p List.mem_cons_self
    have hrest_pages : ∀ r ∈ rest, r ∈ pages :=
      fun r hr => hreqs r (List.mem_cons_of_mem p hr)
    rw [offlineLookahead_cons]
    split_ifs with hps hslt
    · exact ⟨validStep_hit hscard hps,
        validSchedule_offlineLookahead hk p₀ hnodup hlen rest hscard hsub hrest_pages⟩
    · have hstep := validStep_insert hslt hps
      exact ⟨hstep, validSchedule_offlineLookahead hk p₀ hnodup hlen rest hstep.2.1
        (Finset.insert_subset (List.mem_toFinset.mpr hp_pages) hsub) hrest_pages⟩
    · have hseq : s.card = k := by omega
      obtain ⟨hev_s, hev_not⟩ := evict_mem_and_notMem p₀ hnodup hsub hseq rest hk
      set evict := missingPage p₀ (pages.filter (· ∈ s)) (rest.take (k - 1)).toFinset
      set s' := insert p (s.erase evict)
      have hs'_card : s'.card = k := (card_insert_erase_of_notMem hps hev_s).trans hseq
      have hs'_sub : s' ⊆ pages.toFinset := Finset.insert_subset
        (List.mem_toFinset.mpr hp_pages) ((Finset.erase_subset _ _).trans hsub)
      refine ⟨validStep_replace hscard hps hev_s, ?_⟩
      have hwarm_sched := validSchedule_replicate_of_forall_mem (Nat.le_of_eq hs'_card)
        (warm_mem_next_cache hnodup hlen hsub hseq hp_pages hps hev_not hrest_pages)
      have htail_sched := validSchedule_offlineLookahead hk p₀ hnodup hlen (rest.drop (k - 1))
        (Nat.le_of_eq hs'_card) hs'_sub fun r hr => hrest_pages r (List.mem_of_mem_drop hr)
      have happ := (problem α k).validSchedule_append hwarm_sched
        (by rw [finalState_replicate]; exact htail_sched)
      simpa only [List.take_append_drop] using happ
termination_by _ reqs _ _ _ => reqs.length

/-- Fault bound for `offlineLookahead`: `k` times the offline fault count is at most
`reqs.length + (k - 1) * (k - s.card) + (k - 1)`. -/
theorem scheduleCost_offlineLookahead_bound {k : Nat} (hk : 0 < k) (p₀ : α) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1) :
    ∀ {s : Finset α} (reqs : List α),
      s.card ≤ k →
      s ⊆ pages.toFinset →
      (∀ r ∈ reqs, r ∈ pages) →
      k * (problem α k).scheduleCost s reqs (offlineLookahead k p₀ pages s reqs) ≤
        reqs.length + (k - 1) * (k - s.card) + (k - 1)
  | s, [], _, _, _ => by rw [offlineLookahead_nil]; exact Nat.zero_le _
  | s, p :: rest, hscard, hsub, hreqs => by
    have hp_pages : p ∈ pages := hreqs p List.mem_cons_self
    have hrest_pages : ∀ r ∈ rest, r ∈ pages :=
      fun r hr => hreqs r (List.mem_cons_of_mem p hr)
    rw [offlineLookahead_cons]
    split_ifs with hps hslt
    · change k * (stepCost s p s + _) ≤ _
      rw [stepCost_of_mem hps, Nat.zero_add, List.length_cons]
      have ih := scheduleCost_offlineLookahead_bound hk p₀ hnodup hlen rest hscard hsub hrest_pages
      omega
    · change k * (stepCost s p (insert p s) + _) ≤ _
      have hs'_card : (insert p s).card = s.card + 1 := Finset.card_insert_of_notMem hps
      have ih := scheduleCost_offlineLookahead_bound hk p₀ hnodup hlen rest (by omega)
        (Finset.insert_subset (List.mem_toFinset.mpr hp_pages) hsub) hrest_pages
      rw [stepCost_of_notMem hps, Nat.mul_add, Nat.mul_one, List.length_cons,
        show k - s.card = (k - (insert p s).card) + 1 by omega, Nat.mul_add, Nat.mul_one]
      omega
    · have hseq : s.card = k := by omega
      obtain ⟨hev_s, hev_not⟩ := evict_mem_and_notMem p₀ hnodup hsub hseq rest hk
      set evict := missingPage p₀ (pages.filter (· ∈ s)) (rest.take (k - 1)).toFinset
      set s' := insert p (s.erase evict)
      set warm := rest.take (k - 1)
      set tail := rest.drop (k - 1)
      change k * (stepCost s p s' + (problem α k).scheduleCost s' rest
        (List.replicate warm.length s' ++ offlineLookahead k p₀ pages s' tail)) ≤ _
      rw [stepCost_of_notMem hps]
      have hsplit : warm ++ tail = rest := List.take_append_drop (k - 1) rest
      rw [← hsplit,
        (problem α k).scheduleCost_append (List.length_replicate),
        finalState_replicate]
      have hwarm_mem : ∀ q ∈ warm, q ∈ s' :=
        warm_mem_next_cache hnodup hlen hsub hseq hp_pages hps hev_not hrest_pages
      rw [scheduleCost_replicate_of_forall_mem hwarm_mem, Nat.zero_add,
        Nat.mul_add, Nat.mul_one]
      have hs'_card : s'.card = k := (card_insert_erase_of_notMem hps hev_s).trans hseq
      have hs'_sub : s' ⊆ pages.toFinset := Finset.insert_subset
        (List.mem_toFinset.mpr hp_pages) ((Finset.erase_subset _ _).trans hsub)
      have htail_pages : ∀ r ∈ tail, r ∈ pages :=
        fun r hr => hrest_pages r (List.mem_of_mem_drop hr)
      by_cases hshort : rest.length < k - 1
      · dsimp only [tail]
        rw [List.drop_eq_nil_of_le hshort.le]
        change k + k * 0 ≤ _
        simp only [hseq, Nat.sub_self, List.length_cons]
        omega
      · have ih := scheduleCost_offlineLookahead_bound hk p₀ hnodup hlen tail
          (Nat.le_of_eq hs'_card) hs'_sub htail_pages
        have htail_len : tail.length = rest.length - (k - 1) := List.length_drop
        simp only [hsplit, hseq, hs'_card, Nat.sub_self, Nat.mul_zero, Nat.add_zero,
          List.length_cons, htail_len] at ih ⊢
        omega
termination_by _ reqs _ _ _ => reqs.length

/-! ### Competitive-ratio impossibility theorems ([SleatorTarjan1985], Theorem 5) -/

/-- The adversary against `A` on `n` requests, served offline by `offlineLookahead`: `A` faults
on every request, and `k` times the offline cost is at most
`n + (k - 1) * (k - s₀.card) + (k - 1)`. Both lower bounds below start from this instance. -/
private theorem exists_adversary_offline {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) (hs₀_sub : s₀ ⊆ pages.toFinset)
    (A : DetStrategy (problem α k)) (n : Nat) :
    ∃ reqs offStates,
      reqs.length = n ∧
      (problem α k).ValidSchedule s₀ reqs offStates ∧
      A.cost s₀ reqs = n ∧
      k * (problem α k).scheduleCost s₀ reqs offStates ≤
        n + (k - 1) * (k - s₀.card) + (k - 1) := by
  have hpne : pages ≠ [] := by grind
  set p₀ := pages.head hpne
  set reqs := adversaryRequests p₀ pages A s₀ n
  have hreqs_pages : ∀ r ∈ reqs, r ∈ pages :=
    fun r hr => mem_adversaryRequests p₀ hnodup hlen A hs₀ hr
  have hlen_reqs : reqs.length = n := adversaryRequests_length p₀ pages A s₀ n
  refine ⟨reqs, offlineLookahead k p₀ pages s₀ reqs, hlen_reqs,
    validSchedule_offlineLookahead hk p₀ hnodup hlen reqs hs₀ hs₀_sub hreqs_pages,
    cost_adversaryRequests p₀ hnodup hlen A hs₀ n, ?_⟩
  simpa only [hlen_reqs] using
    scheduleCost_offlineLookahead_bound hk p₀ hnodup hlen reqs hs₀ hs₀_sub hreqs_pages

/-- Exact factor-`k` witness from a full initial cache `s₀` (`s₀.card = k`, `s₀ ⊆ pages.toFinset`):
for any `m : Nat` and deterministic online strategy `A`, there is a request sequence of length
`k * m` and a valid offline schedule `offStates` from `s₀` such that `A.cost s₀ reqs = k * m`
while `(problem α k).scheduleCost s₀ reqs offStates ≤ m`. -/
theorem exists_witness_of_card_eq {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    {s₀ : Finset α} (hs₀_card : s₀.card = k) (hs₀_sub : s₀ ⊆ pages.toFinset)
    (A : DetStrategy (problem α k)) (m : Nat) :
    ∃ reqs offStates,
      reqs.length = k * m ∧
      (problem α k).ValidSchedule s₀ reqs offStates ∧
      A.cost s₀ reqs = k * m ∧
      (problem α k).scheduleCost s₀ reqs offStates ≤ m := by
  obtain ⟨reqs, offStates, hlen_reqs, hv, halg, hbound⟩ :=
    exists_adversary_offline hk hnodup hlen (Nat.le_of_eq hs₀_card) hs₀_sub A (k * m)
  rw [hs₀_card, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hbound
  refine ⟨reqs, offStates, hlen_reqs, hv, halg,
    Nat.lt_add_one_iff.mp (Nat.lt_of_mul_lt_mul_left (a := k) ?_)⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **Rational-ratio deterministic `k`-competitive lower bound** ([SleatorTarjan1985], Theorem 5 at
`n_A = n_MIN = k`): over any universe containing `k + 1` distinct pages `pages`, from any valid
initial cache `s₀ ⊆ pages.toFinset` (including `s₀ = ∅`), for any `p, q : Nat` with `p < k * q`
(representing any rational competitive ratio `p / q < k`, including ratios `< 1` at `k = 1`) and any
additive slack `b : Nat`, there exist a request sequence `reqs` and a valid offline schedule
`offStates` from `s₀` such that `p * scheduleCost s₀ reqs offStates + b < q * A.cost s₀ reqs`. -/
theorem exists_ratio_violation_of_lt {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) (hs₀_sub : s₀ ⊆ pages.toFinset)
    (A : DetStrategy (problem α k)) {p q : Nat} (hpq : p < k * q) (b : Nat) :
    ∃ reqs offStates,
      (problem α k).ValidSchedule s₀ reqs offStates ∧
        p * (problem α k).scheduleCost s₀ reqs offStates + b < q * A.cost s₀ reqs := by
  set m := p * k + b + 1
  obtain ⟨reqs, offStates, -, hv, halg, hbound⟩ :=
    exists_adversary_offline hk hnodup hlen hs₀ hs₀_sub A (k * m)
  -- The offline schedule pays fewer than `m + k` faults: its warm-up and final hold add at most
  -- `k * (k - 1) + (k - 1) < k * k` to `k` times its cost.
  have hwarmup : (k - 1) * (k - s₀.card) ≤ k * (k - 1) :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans_eq (Nat.mul_comm _ _)
  have hopt_lt : (problem α k).scheduleCost s₀ reqs offStates < m + k := by
    refine Nat.lt_of_mul_lt_mul_left (a := k) ?_
    have := Nat.mul_sub_one k k
    have := Nat.le_mul_self k
    rw [Nat.mul_add]; omega
  refine ⟨reqs, offStates, hv, ?_⟩
  rw [halg]
  have hp_opt := Nat.mul_le_mul_left p hopt_lt.le
  rw [Nat.mul_add] at hp_opt
  have hpqm : (p + 1) * m ≤ (k * q) * m := Nat.mul_le_mul_right m hpq
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm k q, Nat.mul_assoc] at hpqm
  have hm_def : m = p * k + b + 1 := rfl
  omega

/-- **Deterministic `k`-competitive lower bound from a fixed initial cache** ([SleatorTarjan1985],
Theorem 5 at `n_A = n_MIN = k`): over any universe containing `k + 1` distinct pages `pages`, from
any valid initial cache `s₀ ⊆ pages.toFinset` (including `s₀ = ∅`), no deterministic online paging
strategy is `(c, b)`-competitive for any integer `c < k` and `b : Nat`. -/
theorem not_isCompetitiveFrom_of_lt {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    {s₀ : Finset α} (hs₀ : ValidCache k s₀) (hs₀_sub : s₀ ⊆ pages.toFinset)
    (A : DetStrategy (problem α k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveFrom s₀ c b := by
  intro hcomp
  obtain ⟨reqs, offStates, hv, hlt⟩ := exists_ratio_violation_of_lt hk hnodup hlen hs₀ hs₀_sub A
    (p := c) (q := 1) (by omega) b
  exact Nat.not_le.mpr (Nat.one_mul (A.cost s₀ reqs) ▸ hlt) (hcomp reqs offStates hv)

/-- No deterministic online paging strategy over a universe containing `k + 1` distinct pages is
`(c, b)`-competitive for any `c < k` and `b : Nat`. -/
theorem not_isCompetitive_of_lt {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    (A : DetStrategy (problem α k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitive c b := fun h =>
  not_isCompetitiveFrom_of_lt hk hnodup hlen (validCache_empty k) (Finset.empty_subset _)
    A hc b (h ∅ (validCache_empty k))

/-- No deterministic online paging strategy over a universe containing `k + 1` distinct pages is
`(c, b)`-competitive across arbitrary initial caches for any `c < k` and `b : Nat`. -/
theorem not_isCompetitiveAnyInit_of_lt {k : Nat} (hk : 0 < k) {pages : List α}
    (hnodup : pages.Nodup) (hlen : pages.length = k + 1)
    (A : DetStrategy (problem α k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveAnyInit c b := fun h =>
  not_isCompetitive_of_lt hk hnodup hlen A hc b h.toIsCompetitive

/-! ### Canonical `Fin (k + 1)` specializations -/

/-- Over `Fin (k + 1)` (`0 < k`), from the empty initial cache `∅`, no deterministic online paging
strategy achieves any rational competitive ratio `p / q < k` (`p < k * q`) with any additive slack
`b : Nat`. -/
theorem fin_exists_ratio_violation_empty_of_lt {k : Nat} (hk : 0 < k)
    (A : DetStrategy (problem (Fin (k + 1)) k)) {p q : Nat} (hpq : p < k * q) (b : Nat) :
    ∃ reqs offStates,
      (problem (Fin (k + 1)) k).ValidSchedule ∅ reqs offStates ∧
        p * (problem (Fin (k + 1)) k).scheduleCost ∅ reqs offStates + b < q * A.cost ∅ reqs :=
  exists_ratio_violation_of_lt hk (List.nodup_finRange (k + 1)) (List.length_finRange)
    (validCache_empty k) (Finset.empty_subset _) A hpq b

/-- Over `Fin (k + 1)` (`0 < k`), no deterministic online paging strategy is `(c, b)`-competitive
even from the empty initial cache `∅` when `c < k`. -/
theorem fin_not_isCompetitiveFrom_empty_of_lt {k : Nat} (hk : 0 < k)
    (A : DetStrategy (problem (Fin (k + 1)) k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveFrom ∅ c b :=
  not_isCompetitiveFrom_of_lt hk (List.nodup_finRange (k + 1)) (List.length_finRange)
    (validCache_empty k) (Finset.empty_subset _) A hc b

/-- Over `Fin (k + 1)` (`0 < k`), no deterministic online paging strategy is `(c, b)`-competitive
for any `c < k` and `b : Nat`. -/
theorem fin_not_isCompetitive_of_lt {k : Nat} (hk : 0 < k)
    (A : DetStrategy (problem (Fin (k + 1)) k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitive c b :=
  not_isCompetitive_of_lt hk (List.nodup_finRange (k + 1)) (List.length_finRange) A hc b

/-- Over `Fin (k + 1)` (`0 < k`), no deterministic online paging strategy is `(c, b)`-competitive
across arbitrary initial caches for any `c < k` and `b : Nat`. -/
theorem fin_not_isCompetitiveAnyInit_of_lt {k : Nat} (hk : 0 < k)
    (A : DetStrategy (problem (Fin (k + 1)) k)) {c : Nat} (hc : c < k) (b : Nat) :
    ¬ A.IsCompetitiveAnyInit c b :=
  not_isCompetitiveAnyInit_of_lt hk (List.nodup_finRange (k + 1)) (List.length_finRange) A hc b

end Cslib.DataStructure.Paging
