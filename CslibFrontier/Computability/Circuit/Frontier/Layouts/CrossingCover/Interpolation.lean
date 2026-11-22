/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Submodular
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith

/-!
# Deterministic interpolation from crossing covers to cutwidth

For a loopless cubic multigraph `G` and any vertex bipartition `b : V → Bool`, suppose edge
colorings `x ≤ y : E → Bool` are both clamped at `b`, with `y` minimizing `anchoredCost G b`.
Then the differing edges `U = {e | x e = false ∧ y e = true}` can be flipped one at a time from
`false` to `true` so that every intermediate coloring `z` satisfies

`splitCost G z ≤ anchoredCost G b x + 2`

(`exists_clamped_flip_chain`). The vertices incident to `U` partition into `A` (cost `0 → 1`),
`B` (cost `1 → 0`), and `P` (cost `1 → 1`). Optimality of `y` verifies Hall's marriage condition
from `A` to `B`. After flipping `P`/`B`-only edges (`+0`) and `A`-vertices with no fixed edge
(`+1`), the remaining `A'`-vertices each touch at most two `B`-vertices, so a degree-sum peeling
reduces the excess of started `A'`-blocks over finished `B`-vertices to at most `1` between blocks
and at most `2` mid-block.

Concatenating these monotone transitions along a vertex layout `π` (between consecutive prefixes
`b₀ ≤ b₁ ≤ … ≤ bₙ`) yields an edge permutation whose maximum split cost is at most `M + 3`, where
`M = max_k crossingCover G b_k`. Scoring the edges by position in this permutation and applying
`Multigraph.exists_width_le_of_edgeScore` yields a vertex layout of `G` with width at most `M + 6`
(`exists_width_le_max_crossingCover`).

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.exists_block_peeling_order`: peeling order on a bipartite
  incidence family of left-degree at most two admitting a Hall injection into the right side.
* `Cslib.Circuits.Frontier.CrossingCover.exists_clamped_flip_chain`: `splitCost ≤ anchoredCost + 2`
  interpolation between clamped `x ≤ y` when `y` is optimal.
* `Cslib.Circuits.Frontier.CrossingCover.exists_edge_order_splitCost_le`: concatenation across a
  vertex ordering keeping `splitCost ≤ M + 3`.
* `Cslib.Circuits.Frontier.CrossingCover.exists_width_le_max_crossingCover`: `cw(G) ≤ M + 6`.
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset Function

/-! ### Peeling a 2-regular and Hall-matched block family -/

section Peeling

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The elements of `W` whose incident members of `R` all appear in the prefix `done`. -/
@[expose] def finishedIn (nbr : α → Finset β) (R : Finset α) (W : Finset β)
    (done : List α) : Finset β :=
  open Classical in W.filter fun w => ∀ r ∈ R, w ∈ nbr r → r ∈ done

omit [DecidableEq α] in
private theorem sum_deg_eq_sum_card (nbr : α → Finset β) (R : Finset α) (W : Finset β)
    (hsub : ∀ r ∈ R, nbr r ⊆ W) :
    ∑ w ∈ W, (R.filter fun r => w ∈ nbr r).card = ∑ r ∈ R, (nbr r).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← Finset.card_filter]
  congr 1; ext w
  simp only [mem_filter, and_iff_right_iff_imp]
  exact fun hw => hsub r hr hw

private theorem mem_two_pair {s : Finset β} (hs : s.card = 2) {x : β} (hx : x ∈ s) :
    ∃ y ∈ s, y ≠ x ∧ s = {x, y} := by
  obtain ⟨y, hy⟩ := card_eq_one.mp (show (s.erase x).card = 1 by
    rw [card_erase_of_mem hx, hs])
  have hy_mem : y ∈ s.erase x := hy ▸ mem_singleton_self y
  refine ⟨y, (mem_erase.mp hy_mem).2, (mem_erase.mp hy_mem).1, ?_⟩
  ext z
  by_cases hzx : z = x
  · subst hzx; simp [hx]
  · simp only [mem_insert, mem_singleton, hzx, false_or]
    constructor
    · intro hz
      have : z ∈ s.erase x := mem_erase.mpr ⟨hzx, hz⟩
      rw [hy, mem_singleton] at this; exact this
    · rintro rfl; exact (mem_erase.mp hy_mem).2

private theorem exists_path_peel (nbr : α → Finset β) :
    ∀ n : ℕ, ∀ (R : Finset α) (W : Finset β) (u v : β),
      R.card = n →
      u ∈ W → v ∈ W → u ≠ v →
      (∀ r ∈ R, nbr r ⊆ W ∧ (nbr r).card = 2) →
      (R.filter fun r => u ∈ nbr r).card = 1 →
      (R.filter fun r => v ∈ nbr r).card = 1 →
      (∀ w ∈ W, w ≠ u → w ≠ v → (R.filter fun r => w ∈ nbr r).card = 2) →
      ∃ (p : List α) (S : Finset α) (V : Finset β),
        p.Nodup ∧ (∀ r, r ∈ p ↔ r ∈ S) ∧ S ⊆ R ∧ V ⊆ W ∧ u ∈ V ∧ v ∈ V ∧
        p.length + 1 = V.card ∧
        (∀ r ∈ R \ S, nbr r ⊆ W \ V) ∧
        (∀ r ∈ S, nbr r ⊆ V) ∧
        (∀ w ∈ W \ V, ((R \ S).filter fun r => w ∈ nbr r).card = 2) ∧
        (∀ k ≤ p.length, k < p.length →
          k ≤ (finishedIn nbr R V (p.take k)).card) ∧
        (∀ w ∈ V, ∀ r ∈ R, w ∈ nbr r → r ∈ p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro R W u v hcard hu hv huv hnbr hdu hdv hdeg
    obtain ⟨r, hr_eq⟩ := card_eq_one.mp hdu
    have hr_mem : r ∈ R.filter fun r => u ∈ nbr r := hr_eq ▸ mem_singleton_self r
    have hrR : r ∈ R := (mem_filter.mp hr_mem).1
    have hur : u ∈ nbr r := (mem_filter.mp hr_mem).2
    have hruniq : ∀ r' ∈ R, u ∈ nbr r' → r' = r := fun r' hr' hur' => by
      have : r' ∈ ({r} : Finset α) := hr_eq ▸ mem_filter.mpr ⟨hr', hur'⟩
      exact mem_singleton.mp this
    obtain ⟨w, hwr, hwu, hpair⟩ := mem_two_pair (hnbr r hrR).2 hur
    have hwW : w ∈ W := (hnbr r hrR).1 hwr
    by_cases hvw : w = v
    · subst hvw
      have hr_uniq_v : ∀ r' ∈ R, w ∈ nbr r' → r' = r := fun r' hr' hwr' => by
        obtain ⟨r0, hr0⟩ := card_eq_one.mp hdv
        have h1 : r ∈ ({r0} : Finset α) := hr0 ▸ mem_filter.mpr ⟨hrR, hwr⟩
        have h2 : r' ∈ ({r0} : Finset α) := hr0 ▸ mem_filter.mpr ⟨hr', hwr'⟩
        rw [mem_singleton.mp h1, mem_singleton.mp h2]
      refine ⟨[r], {r}, {u, w}, List.nodup_singleton r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
      · intro x; simp
      · exact singleton_subset_iff.mpr hrR
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hu
        · rw [mem_singleton.mp hx]; exact hwW
      · simp
      · simp
      · rw [List.length_singleton, card_pair huv]
      · intro r' hr' z hz
        rw [mem_sdiff, mem_singleton] at hr'
        refine mem_sdiff.mpr ⟨(hnbr r' hr'.1).1 hz, fun hzuw => ?_⟩
        rcases mem_insert.mp hzuw with rfl | hzw
        · exact hr'.2 (hruniq r' hr'.1 hz)
        · rw [mem_singleton.mp hzw] at hz; exact hr'.2 (hr_uniq_v r' hr'.1 hz)
      · intro r' hr'; rw [mem_singleton.mp hr', hpair]
      · intro z hz
        rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hz
        have hfilt : (R \ {r}).filter (fun r' => z ∈ nbr r') =
            R.filter (fun r' => z ∈ nbr r') := by
          ext r'
          simp only [mem_filter, mem_sdiff, mem_singleton]
          refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
          rintro rfl
          rw [hpair, mem_insert, mem_singleton] at h
          rcases h.2 with rfl | rfl <;> tauto
        rw [hfilt]; exact hdeg z hz.1 hz.2.1 hz.2.2
      · intro k _ hk; have hk0 : k = 0 := by simpa using hk
        rw [hk0]; exact Nat.zero_le _
      · intro z hz r' hr' hzr'
        rcases mem_insert.mp hz with rfl | hzw
        · simp [hruniq r' hr' hzr']
        · rw [mem_singleton.mp hzw] at hzr'; simp [hr_uniq_v r' hr' hzr']
    · set R' := R.erase r
      set W' := W.erase u
      have hcard' : R'.card < n := by rw [← hcard]; exact card_erase_lt_of_mem hrR
      have hwW' : w ∈ W' := mem_erase.mpr ⟨hwu, hwW⟩
      have hvW' : v ∈ W' := mem_erase.mpr ⟨huv.symm, hv⟩
      have hnbr' : ∀ r' ∈ R', nbr r' ⊆ W' ∧ (nbr r').card = 2 := fun r' hr' => by
        refine ⟨fun z hz => mem_erase.mpr ⟨fun hzu => ?_, (hnbr r' (erase_subset _ _ hr')).1 hz⟩,
          (hnbr r' (erase_subset _ _ hr')).2⟩
        subst hzu
        exact (mem_erase.mp hr').1 (hruniq r' (erase_subset _ _ hr') hz)
      have hdw' : (R'.filter fun r' => w ∈ nbr r').card = 1 := by
        have hfilt : R'.filter (fun r' => w ∈ nbr r') =
            (R.filter fun r' => w ∈ nbr r').erase r := by
          ext r'; simp only [R', mem_filter, mem_erase]; tauto
        rw [hfilt, card_erase_of_mem (mem_filter.mpr ⟨hrR, hwr⟩), hdeg w hwW hwu hvw]
      have hdv' : (R'.filter fun r' => v ∈ nbr r').card = 1 := by
        have hfilt : R'.filter (fun r' => v ∈ nbr r') = R.filter fun r' => v ∈ nbr r' := by
          ext r'; simp only [R', mem_filter, mem_erase]
          refine ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨?_, h.1⟩, h.2⟩⟩
          rintro rfl
          rw [hpair, mem_insert, mem_singleton] at h
          rcases h.2 with h1 | h2
          · exact huv h1.symm
          · exact hvw h2.symm
        rw [hfilt, hdv]
      have hdeg' : ∀ z ∈ W', z ≠ w → z ≠ v → (R'.filter fun r' => z ∈ nbr r').card = 2 := by
        intro z hz hzw hzv
        have hzW : z ∈ W := (mem_erase.mp hz).2
        have hzu : z ≠ u := (mem_erase.mp hz).1
        have hfilt : R'.filter (fun r' => z ∈ nbr r') = R.filter fun r' => z ∈ nbr r' := by
          ext r'; simp only [R', mem_filter, mem_erase]
          refine ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨?_, h.1⟩, h.2⟩⟩
          rintro rfl
          rw [hpair, mem_insert, mem_singleton] at h
          rcases h.2 with h1 | h2 <;> tauto
        rw [hfilt]; exact hdeg z hzW hzu hzv
      obtain ⟨p, S, V, hpnd, hpS, hSR', hVW', hwV, hvV, hlen, hrest, hSin, hrestdeg, hfin,
        hVcov⟩ := ih R'.card hcard' R' W' w v rfl hwW' hvW' hvw hnbr' hdw' hdv' hdeg'
      have hrp : r ∉ p := fun hr => (mem_erase.mp (hSR' ((hpS r).mp hr))).1 rfl
      have hrS : r ∉ S := fun hr => hrp ((hpS r).mpr hr)
      have huV : u ∉ V := fun h => (mem_erase.mp (hVW' h)).1 rfl
      refine ⟨r :: p, insert r S, insert u V, List.nodup_cons.mpr ⟨hrp, hpnd⟩, ?_, ?_, ?_,
        mem_insert_self u V, mem_insert_of_mem hvV, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x; simp [hpS]
      · exact insert_subset_iff.mpr ⟨hrR, hSR'.trans (erase_subset _ _)⟩
      · exact insert_subset_iff.mpr ⟨hu, hVW'.trans (erase_subset _ _)⟩
      · rw [List.length_cons, card_insert_of_notMem huV, hlen]
      · intro r' hr'
        have hr'eq : R \ insert r S = R' \ S := by
          ext x; simp only [mem_sdiff, mem_insert, R', mem_erase]; tauto
        have hWeq : W \ insert u V = W' \ V := by
          ext x; simp only [mem_sdiff, mem_insert, W', mem_erase]; tauto
        rw [hr'eq] at hr'; rw [hWeq]; exact hrest r' hr'
      · intro r' hr'
        rcases mem_insert.mp hr' with rfl | hrS'
        · rw [hpair]; intro z hz
          rcases mem_insert.mp hz with rfl | hz
          · exact mem_insert_self _ V
          · rw [mem_singleton.mp hz]; exact mem_insert_of_mem hwV
        · exact (hSin r' hrS').trans (subset_insert u V)
      · intro z hz
        have hr'eq : R \ insert r S = R' \ S := by
          ext x; simp only [mem_sdiff, mem_insert, R', mem_erase]; tauto
        have hWeq : W \ insert u V = W' \ V := by
          ext x; simp only [mem_sdiff, mem_insert, W', mem_erase]; tauto
        rw [hWeq] at hz; rw [hr'eq]; exact hrestdeg z hz
      · intro k hk hlt
        cases k with
        | zero => simp
        | succ k' =>
          have hlt' : k' < p.length := by simpa using hlt
          have hle' : k' ≤ p.length := hlt'.le
          have hsub_fin : insert u (finishedIn nbr R' V (p.take k')) ⊆
              finishedIn nbr R (insert u V) ((r :: p).take (k' + 1)) := by
            intro z hz
            rcases mem_insert.mp hz with rfl | hz'
            · refine mem_filter.mpr ⟨mem_insert_self _ V, fun r' hr' hur' => ?_⟩
              rw [hruniq r' hr' hur']; simp
            · rw [finishedIn, mem_filter] at hz'
              refine mem_filter.mpr ⟨mem_insert_of_mem hz'.1, fun r' hr' hzr' => ?_⟩
              by_cases hrr' : r' = r
              · subst hrr'; simp
              · exact List.mem_cons_of_mem r (hz'.2 r' (mem_erase.mpr ⟨hrr', hr'⟩) hzr')
          have hunot : u ∉ finishedIn nbr R' V (p.take k') := fun h =>
            huV (mem_filter.mp h).1
          calc k' + 1 ≤ (finishedIn nbr R' V (p.take k')).card + 1 :=
                Nat.add_le_add_right (hfin k' hle' hlt') 1
            _ = (insert u (finishedIn nbr R' V (p.take k'))).card :=
                (card_insert_of_notMem hunot).symm
            _ ≤ (finishedIn nbr R (insert u V) ((r :: p).take (k' + 1))).card :=
                card_le_card hsub_fin
      · intro z hz r' hr' hzr'
        rcases mem_insert.mp hz with rfl | hzV
        · rw [hruniq r' hr' hzr']; exact List.mem_cons_self
        · by_cases hrr' : r' = r
          · subst hrr'; exact List.mem_cons_self
          · exact List.mem_cons_of_mem r (hVcov z hzV r' (mem_erase.mpr ⟨hrr', hr'⟩) hzr')

private theorem exists_twoReg_peel (nbr : α → Finset β) :
    ∀ n : ℕ, ∀ (R : Finset α) (W : Finset β),
      R.card = n →
      (∀ r ∈ R, nbr r ⊆ W ∧ (nbr r).card = 2) →
      (∀ w ∈ W, (R.filter fun r => w ∈ nbr r).card = 2) →
      ∃ ord : List α, ord.Nodup ∧ (∀ r, r ∈ ord ↔ r ∈ R) ∧
        ∀ k ≤ ord.length, k ≤ (finishedIn nbr R W (ord.take k)).card + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro R W hcard hnbr hdeg
    rcases R.eq_empty_or_nonempty with rfl | ⟨r₀, hr₀⟩
    · exact ⟨[], List.nodup_nil, fun r => by simp, fun k hk => by
        have hk0 : k = 0 := Nat.le_zero.mp (by simpa using hk)
        rw [hk0]; exact Nat.zero_le _⟩
    obtain ⟨u, hu⟩ := card_pos.mp (by rw [(hnbr r₀ hr₀).2]; omega : 0 < (nbr r₀).card)
    obtain ⟨v, hv, hvu, hpair⟩ := mem_two_pair (hnbr r₀ hr₀).2 hu
    have huW : u ∈ W := (hnbr r₀ hr₀).1 hu
    have hvW : v ∈ W := (hnbr r₀ hr₀).1 hv
    set R₁ := R.erase r₀
    have hnbr₁ : ∀ r ∈ R₁, nbr r ⊆ W ∧ (nbr r).card = 2 :=
      fun r hr => hnbr r (erase_subset _ _ hr)
    have hdu : (R₁.filter fun r => u ∈ nbr r).card = 1 := by
      have hfilt : R₁.filter (fun r => u ∈ nbr r) =
          (R.filter fun r => u ∈ nbr r).erase r₀ := by
        ext r; simp only [R₁, mem_filter, mem_erase]; tauto
      rw [hfilt, card_erase_of_mem (mem_filter.mpr ⟨hr₀, hu⟩), hdeg u huW]
    have hdv : (R₁.filter fun r => v ∈ nbr r).card = 1 := by
      have hfilt : R₁.filter (fun r => v ∈ nbr r) =
          (R.filter fun r => v ∈ nbr r).erase r₀ := by
        ext r; simp only [R₁, mem_filter, mem_erase]; tauto
      rw [hfilt, card_erase_of_mem (mem_filter.mpr ⟨hr₀, hv⟩), hdeg v hvW]
    have hdeg₁ : ∀ w ∈ W, w ≠ u → w ≠ v → (R₁.filter fun r => w ∈ nbr r).card = 2 := by
      intro w hw hwu hwv
      have hfilt : R₁.filter (fun r => w ∈ nbr r) = R.filter fun r => w ∈ nbr r := by
        ext r; simp only [R₁, mem_filter, mem_erase]
        refine ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨?_, h.1⟩, h.2⟩⟩
        rintro rfl
        rw [hpair, mem_insert, mem_singleton] at h
        rcases h.2 with h1 | h2 <;> tauto
      rw [hfilt]; exact hdeg w hw
    obtain ⟨p, S, V, hpnd, hpS, hSR₁, hVW, huV, hvV, hlen, hrest_in, hSin, hrest_deg, hfin,
      hVcov⟩ := exists_path_peel nbr R₁.card R₁ W u v rfl huW hvW hvu.symm hnbr₁ hdu hdv hdeg₁
    set R' := R₁ \ S
    set W' := W \ V
    have hr₀S : r₀ ∉ S := fun h => (mem_erase.mp (hSR₁ h)).1 rfl
    have hr₀p : r₀ ∉ p := fun h => hr₀S ((hpS r₀).mp h)
    have hcard' : R'.card < n := by
      rw [← hcard]
      exact (card_le_card sdiff_subset).trans_lt (card_erase_lt_of_mem hr₀)
    have hnbr' : ∀ r ∈ R', nbr r ⊆ W' ∧ (nbr r).card = 2 :=
      fun r hr => ⟨hrest_in r hr, (hnbr₁ r (sdiff_subset hr)).2⟩
    obtain ⟨q, hqnd, hqR', hqfin⟩ := ih R'.card hcard' R' W' rfl hnbr' hrest_deg
    have hdisj : ∀ r ∈ r₀ :: p, r ∉ q := by
      intro r hr hq
      have hrq := (hqR' r).mp hq
      rcases List.mem_cons.mp hr with rfl | hrp
      · exact (mem_erase.mp (mem_sdiff.mp hrq).1).1 rfl
      · exact (mem_sdiff.mp hrq).2 ((hpS r).mp hrp)
    refine ⟨(r₀ :: p) ++ q, ?_, ?_, ?_⟩
    · exact (List.nodup_cons.mpr ⟨hr₀p, hpnd⟩).append hqnd (fun x hx => hdisj x hx)
    · intro r
      simp only [List.mem_append, List.mem_cons, hpS, hqR', R', mem_sdiff, R₁, mem_erase]
      constructor
      · rintro ((rfl | hrS) | ⟨⟨_, hrR⟩, _⟩)
        · exact hr₀
        · exact (mem_erase.mp (hSR₁ hrS)).2
        · exact hrR
      · intro hrR
        by_cases h0 : r = r₀
        · left; left; exact h0
        · by_cases hS : r ∈ S
          · left; right; exact hS
          · right; exact ⟨⟨h0, hrR⟩, hS⟩
    · intro k hk
      by_cases hk1 : k < p.length + 1
      · cases k with
        | zero => simp
        | succ m =>
          have hm : m < p.length := by omega
          have htake : ((r₀ :: p) ++ q).take (m + 1) = r₀ :: p.take m := by
            rw [List.take_append_of_le_length (by simp; omega), List.take_succ_cons]
          rw [htake]
          have hsub : finishedIn nbr R₁ V (p.take m) ⊆ finishedIn nbr R W (r₀ :: p.take m) := by
            intro w hw
            rw [finishedIn, mem_filter] at hw ⊢
            refine ⟨hVW hw.1, fun r hr hwr => ?_⟩
            by_cases h0 : r = r₀
            · subst h0; exact List.mem_cons_self
            · exact List.mem_cons_of_mem r₀ (hw.2 r (mem_erase.mpr ⟨h0, hr⟩) hwr)
          calc m + 1 ≤ (finishedIn nbr R₁ V (p.take m)).card + 1 :=
                Nat.add_le_add_right (hfin m hm.le hm) 1
            _ ≤ (finishedIn nbr R W (r₀ :: p.take m)).card + 1 :=
                Nat.add_le_add_right (card_le_card hsub) 1
      · have hge : p.length + 1 ≤ k := by omega
        set t := k - (p.length + 1)
        have htk : k = (p.length + 1) + t := by omega
        have ht_le : t ≤ q.length := by
          simp only [List.length_append, List.length_cons] at hk; omega
        have htake : ((r₀ :: p) ++ q).take k = (r₀ :: p) ++ q.take t := by
          rw [htk, show p.length + 1 = (r₀ :: p).length from rfl,
            List.take_append, List.take_of_length_le (Nat.le_add_right _ _)]
          simp
        rw [htake]
        have hVfin : V ⊆ finishedIn nbr R W ((r₀ :: p) ++ q.take t) := fun w hw => by
          refine mem_filter.mpr ⟨hVW hw, fun r hr hwr => ?_⟩
          apply List.mem_append_left
          by_cases h0 : r = r₀
          · subst h0; exact List.mem_cons_self
          · exact List.mem_cons_of_mem r₀ (hVcov w hw r (mem_erase.mpr ⟨h0, hr⟩) hwr)
        have hW'fin : finishedIn nbr R' W' (q.take t) ⊆
            finishedIn nbr R W ((r₀ :: p) ++ q.take t) := fun w hw => by
          rw [finishedIn, mem_filter] at hw ⊢
          refine ⟨(mem_sdiff.mp hw.1).1, fun r hr hwr => ?_⟩
          by_cases h0 : r = r₀
          · subst h0; exact List.mem_append_left _ List.mem_cons_self
          · by_cases hS : r ∈ S
            · exact List.mem_append_left _ (List.mem_cons_of_mem r₀ ((hpS r).mpr hS))
            · exact List.mem_append_right _
                (hw.2 r (mem_sdiff.mpr ⟨mem_erase.mpr ⟨h0, hr⟩, hS⟩) hwr)
        have hdisj_VW : Disjoint V (finishedIn nbr R' W' (q.take t)) :=
          Finset.disjoint_left.mpr fun w hw h2 => (mem_sdiff.mp (mem_filter.mp h2).1).2 hw
        calc k = (p.length + 1) + t := htk
          _ = V.card + t := by rw [hlen]
          _ ≤ V.card + ((finishedIn nbr R' W' (q.take t)).card + 1) :=
              Nat.add_le_add_left (hqfin t ht_le) _
          _ = (V ∪ finishedIn nbr R' W' (q.take t)).card + 1 := by
              rw [card_union_of_disjoint hdisj_VW]; omega
          _ ≤ (finishedIn nbr R W ((r₀ :: p) ++ q.take t)).card + 1 :=
              Nat.add_le_add_right (card_le_card (union_subset hVfin hW'fin)) 1

private theorem eq_of_sum_eq_of_le {γ : Type*} {s : Finset γ} {f g : γ → ℕ}
    (hle : ∀ x ∈ s, f x ≤ g x) (heq : ∑ x ∈ s, f x = ∑ x ∈ s, g x) :
    ∀ x ∈ s, f x = g x := by
  intro x hx
  by_contra hne
  have hlt : f x < g x := lt_of_le_of_ne (hle x hx) hne
  have hsum_lt : ∑ y ∈ s, f y < ∑ y ∈ s, g y := sum_lt_sum hle ⟨x, hx, hlt⟩
  omega

/-- **Peeling order for a Hall-matched bipartite incidence family of left-degree ≤ 2.**
At every completed block prefix `ord.take k`, the deficit `k - |finished W|` is at most `1`. -/
theorem exists_block_peeling_order (nbr : α → Finset β) :
    ∀ m : ℕ, ∀ (R : Finset α) (W : Finset β) (matchB : α → β),
      R.card + W.card = m →
      (∀ r ∈ R, nbr r ⊆ W ∧ (nbr r).card ≤ 2) →
      (∀ r ∈ R, matchB r ∈ nbr r) →
      Set.InjOn matchB (R : Set α) →
      ∃ ord : List α, ord.Nodup ∧ (∀ r, r ∈ ord ↔ r ∈ R) ∧
        ∀ k ≤ ord.length, k ≤ (finishedIn nbr R W (ord.take k)).card + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro R W matchB hsum hnbr hmatch hinj
    rcases R.eq_empty_or_nonempty with rfl | _
    · exact ⟨[], List.nodup_nil, fun r => by simp, fun k hk => by
        have hk0 : k = 0 := Nat.le_zero.mp (by simpa using hk)
        rw [hk0]; exact Nat.zero_le _⟩
    by_cases hzero : ∃ w ∈ W, (R.filter fun r => w ∈ nbr r).card = 0
    · obtain ⟨w, hwW, hdeg0⟩ := hzero
      have hno : ∀ r ∈ R, w ∉ nbr r := fun r hr hwr => by
        have : r ∈ R.filter fun r => w ∈ nbr r := mem_filter.mpr ⟨hr, hwr⟩
        rw [card_eq_zero.mp hdeg0] at this; exact notMem_empty r this
      set W' := W.erase w
      have hlt : R.card + W'.card < m := by
        rw [← hsum, card_erase_of_mem hwW]
        exact Nat.add_lt_add_left (Nat.pred_lt (card_pos.mpr ⟨w, hwW⟩).ne') _
      obtain ⟨ord, hnd, hmem, hbd⟩ := ih (R.card + W'.card) hlt R W' matchB rfl
        (fun r hr => ⟨fun z hz => mem_erase.mpr ⟨fun h => hno r hr (h ▸ hz), (hnbr r hr).1 hz⟩,
          (hnbr r hr).2⟩) hmatch hinj
      refine ⟨ord, hnd, hmem, fun k hk => (hbd k hk).trans ?_⟩
      exact Nat.add_le_add_right (card_le_card fun z hz =>
        mem_filter.mpr ⟨erase_subset _ _ (mem_filter.mp hz).1, (mem_filter.mp hz).2⟩) 1
    push Not at hzero
    by_cases hone : ∃ w ∈ W, (R.filter fun r => w ∈ nbr r).card = 1
    · obtain ⟨w, hwW, hdeg1⟩ := hone
      obtain ⟨r, hr_eq⟩ := card_eq_one.mp hdeg1
      have hrR : r ∈ R := (mem_filter.mp (hr_eq ▸ mem_singleton_self r)).1
      have hruniq : ∀ r' ∈ R, w ∈ nbr r' → r' = r := fun r' hr' hwr' =>
        mem_singleton.mp (hr_eq ▸ mem_filter.mpr ⟨hr', hwr'⟩)
      set R' := R.erase r
      set W' := W.erase w
      have hlt : R'.card + W'.card < m := by
        rw [← hsum, card_erase_of_mem hrR, card_erase_of_mem hwW]
        have h1 : 0 < R.card := card_pos.mpr ⟨r, hrR⟩
        have h2 : 0 < W.card := card_pos.mpr ⟨w, hwW⟩
        omega
      have hnbr' : ∀ r' ∈ R', nbr r' ⊆ W' ∧ (nbr r').card ≤ 2 := fun r' hr' =>
        ⟨fun z hz => mem_erase.mpr ⟨fun hzw =>
            (mem_erase.mp hr').1 (hruniq r' (erase_subset _ _ hr') (hzw ▸ hz)),
            (hnbr r' (erase_subset _ _ hr')).1 hz⟩,
          (hnbr r' (erase_subset _ _ hr')).2⟩
      obtain ⟨ord, hnd, hmem, hbd⟩ := ih (R'.card + W'.card) hlt R' W' matchB rfl hnbr'
        (fun r' hr' => hmatch r' (erase_subset _ _ hr'))
        (hinj.mono (by intro x hx; exact erase_subset _ _ hx))
      have hr_not : r ∉ ord := fun h => (mem_erase.mp ((hmem r).mp h)).1 rfl
      refine ⟨r :: ord, List.nodup_cons.mpr ⟨hr_not, hnd⟩, ?_, ?_⟩
      · intro x; simp only [List.mem_cons, hmem, R', mem_erase]
        exact ⟨fun h => h.elim (fun e => e ▸ hrR) (·.2),
          fun h => by by_cases e : x = r <;> tauto⟩
      · intro k hk
        cases k with
        | zero => simp
        | succ k' =>
          have hk' : k' ≤ ord.length := by simpa using hk
          have hsub : insert w (finishedIn nbr R' W' (ord.take k')) ⊆
              finishedIn nbr R W ((r :: ord).take (k' + 1)) := by
            intro z hz
            rcases mem_insert.mp hz with rfl | hz'
            · refine mem_filter.mpr ⟨hwW, fun r' hr' hwr' => ?_⟩
              rw [hruniq r' hr' hwr']; simp
            · refine mem_filter.mpr ⟨erase_subset _ _ (mem_filter.mp hz').1,
                fun r' hr' hzr' => ?_⟩
              by_cases e : r' = r
              · subst e; simp
              · exact List.mem_cons_of_mem r
                  ((mem_filter.mp hz').2 r' (mem_erase.mpr ⟨e, hr'⟩) hzr')
          have hw_not : w ∉ finishedIn nbr R' W' (ord.take k') := fun h =>
            (mem_erase.mp (mem_filter.mp h).1).1 rfl
          calc k' + 1 ≤ ((finishedIn nbr R' W' (ord.take k')).card + 1) + 1 :=
                Nat.add_le_add_right (hbd k' hk') 1
            _ = (insert w (finishedIn nbr R' W' (ord.take k'))).card + 1 := by
                rw [card_insert_of_notMem hw_not]
            _ ≤ (finishedIn nbr R W ((r :: ord).take (k' + 1))).card + 1 :=
                Nat.add_le_add_right (card_le_card hsub) 1
    push Not at hone
    -- Every `w ∈ W` has degree ≥ 2, while `R` injects into `W` and each `r ∈ R` has `|nbr r| ≤ 2`.
    have hge2 : ∀ w ∈ W, 2 ≤ (R.filter fun r => w ∈ nbr r).card := fun w hw => by
      have h0 := hzero w hw; have h1 := hone w hw; omega
    have hRW : R.card ≤ W.card := by
      have hImg : R.image matchB ⊆ W := fun z hz => by
        obtain ⟨r, hr, rfl⟩ := mem_image.mp hz
        exact (hnbr r hr).1 (hmatch r hr)
      calc R.card = (R.image matchB).card := (card_image_of_injOn hinj).symm
        _ ≤ W.card := card_le_card hImg
    have hsum1 : 2 * W.card ≤ ∑ w ∈ W, (R.filter fun r => w ∈ nbr r).card := by
      calc 2 * W.card = ∑ _w ∈ W, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ _ := sum_le_sum fun w hw => hge2 w hw
    have hsum2 : ∑ r ∈ R, (nbr r).card ≤ 2 * R.card := by
      calc ∑ r ∈ R, (nbr r).card ≤ ∑ _r ∈ R, 2 := sum_le_sum fun r hr => (hnbr r hr).2
        _ = 2 * R.card := by rw [sum_const, smul_eq_mul, mul_comm]
    have hsum_eq := sum_deg_eq_sum_card nbr R W fun r hr => (hnbr r hr).1
    have hR_eq : ∀ r ∈ R, (nbr r).card = 2 := by
      have heq : ∑ r ∈ R, (nbr r).card = ∑ _r ∈ R, 2 := by
        rw [sum_const, smul_eq_mul, mul_comm]; omega
      exact fun r hr => eq_of_sum_eq_of_le (fun x hx => (hnbr x hx).2) heq r hr
    have hW_eq : ∀ w ∈ W, (R.filter fun r => w ∈ nbr r).card = 2 := by
      have heq : ∑ _w ∈ W, 2 = ∑ w ∈ W, (R.filter fun r => w ∈ nbr r).card := by
        rw [sum_const, smul_eq_mul, mul_comm]; omega
      exact fun w hw => (eq_of_sum_eq_of_le (fun x hx => hge2 x hx) heq w hw).symm
    exact exists_twoReg_peel nbr R.card R W rfl
      (fun r hr => ⟨(hnbr r hr).1, hR_eq r hr⟩) hW_eq

end Peeling

/-! ### Edge-flip interpolation between clamped colorings `x ≤ y` -/

section Chain

variable {V E : Type*} [Fintype V] [Finite E] [DecidableEq E]
  (G : Multigraph V E)

/-- Set all edges in `l` to `true`, leaving every other edge at its value in `x`. -/
@[expose] def flipPrefix {E : Type*} [DecidableEq E] (x : E → Bool) (l : List E) : E → Bool :=
  fun e => x e || decide (e ∈ l)

private def setDiffEdges {E : Type*} [Fintype E] (x y : E → Bool) : Finset E :=
  univ.filter fun e => x e = false ∧ y e = true

@[simp] private theorem flipPrefix_nil {E : Type*} [DecidableEq E] (x : E → Bool) :
    flipPrefix x [] = x := by
  ext e; simp [flipPrefix]

private theorem flatMap_take_prefix_decomp {γ δ : Type*} {f : γ → List δ} (xs : List γ) (r : ℕ)
    (hr : r ≤ (xs.flatMap f).length) :
    ∃ j ≤ xs.length,
      (∀ x ∈ xs.take j, ∀ e ∈ f x, e ∈ (xs.flatMap f).take r) ∧
      (∀ e ∈ (xs.flatMap f).take r, ∃ x ∈ xs.take (j + 1), e ∈ f x) := by
  induction xs generalizing r with
  | nil => exact ⟨0, le_rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append] at hr ⊢
    by_cases hlt : r < (f a).length
    · refine ⟨0, Nat.zero_le _, fun _ h => by simp at h, fun e he => ?_⟩
      rw [List.take_append_of_le_length hlt.le] at he
      exact ⟨a, by simp, List.mem_of_mem_take he⟩
    · have hge : (f a).length ≤ r := by omega
      obtain ⟨j, hj, hdone, hextra⟩ := ih (r - (f a).length) (by omega)
      refine ⟨j + 1, by simp; omega, ?_, ?_⟩
      · intro x hx e he
        rw [List.take_append, List.take_of_length_le hge]
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact List.mem_append_left _ he
        · exact List.mem_append_right _ (hdone x hxt e he)
      · intro e he
        rw [List.take_append, List.take_of_length_le hge] at he
        rcases List.mem_append.mp he with he1 | he2
        · exact ⟨a, by simp, he1⟩
        · obtain ⟨x, hx, hfx⟩ := hextra e he2
          exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- **Hall-matching interpolation (single-bipartition step).** If `G` has maximum degree at most
`3`, `x` and `y` are both clamped at `b`, and `y` minimizes `anchoredCost G b`, then the
differing edges `U = {e | x e = false ∧ y e = true}` admit an ordering `l` such that every
intermediate prefix `z = x ∨ (· ∈ l.take k)` keeps `splitCost G z ≤ anchoredCost G b x + 2`. -/
theorem exists_clamped_flip_chain (hd : G.MaxDegreeLE 3)
    {b : V → Bool} {x y : E → Bool}
    (hx : IsClamped G b x) (hy : IsClamped G b y)
    (hym : anchoredCost G b y = crossingCover G b) :
    ∃ l : List E, l.Nodup ∧ (∀ e, e ∈ l ↔ x e = false ∧ y e = true) ∧
      ∀ k ≤ l.length, splitCost G (flipPrefix x (l.take k)) ≤ anchoredCost G b x + 2 := by
  classical
  have := Fintype.ofFinite E
  let U : Finset E := univ.filter fun e => x e = false ∧ y e = true
  have hU_mem : ∀ e, e ∈ U ↔ x e = false ∧ y e = true := fun e => by
    simp [U]
  have hU_opp : ∀ e ∈ U, b (G.src e) ≠ b (G.tgt e) := fun e he heq => by
    have ⟨hxf, hyt⟩ := (hU_mem e).mp he
    have h1 := (isClamped_iff_eq G b x).mp hx e heq
    have h2 := (isClamped_iff_eq G b y).mp hy e heq
    rw [hxf] at h1; rw [hyt] at h2
    exact absurd (h1.trans h2.symm) (by decide)
  -- Partition vertices incident to `U` into `A` (0,1), `B` (1,0), `P` (1,1).
  let touchesU (v : V) : Prop := ∃ e ∈ U, e ∈ G.incidenceSet v
  let A : Finset V := univ.filter fun v => touchesU v ∧ vertexPenalty G b x v = 0
  let B : Finset V := univ.filter fun v => touchesU v ∧ vertexPenalty G b y v = 0
  let P : Finset V := univ.filter fun v =>
    touchesU v ∧ vertexPenalty G b x v = 1 ∧ vertexPenalty G b y v = 1
  let O : Finset V := univ.filter fun v => ¬touchesU v
  have hA_bits : ∀ v ∈ A, b v = false ∧ ∀ e, e ∈ G.incidenceSet v → x e = false := by
    intro v hv
    obtain ⟨⟨e, heU, hev⟩, hpen⟩ := (mem_filter.mp hv).2
    have hall : ∀ e', e' ∈ G.incidenceSet v → x e' = b v := by
      by_contra h; exact absurd ((vertexPenalty_of_not_forall G h).symm.trans hpen) (by decide)
    have hbv : b v = false := (hall e hev).symm.trans ((hU_mem e).mp heU).1
    exact ⟨hbv, fun e' he' => (hall e' he').trans hbv⟩
  have hB_bits : ∀ v ∈ B, b v = true ∧ ∀ e, e ∈ G.incidenceSet v → y e = true := by
    intro v hv
    obtain ⟨⟨e, heU, hev⟩, hpen⟩ := (mem_filter.mp hv).2
    have hall : ∀ e', e' ∈ G.incidenceSet v → y e' = b v := by
      by_contra h; exact absurd ((vertexPenalty_of_not_forall G h).symm.trans hpen) (by decide)
    have hbv : b v = true := (hall e hev).symm.trans ((hU_mem e).mp heU).2
    exact ⟨hbv, fun e' he' => (hall e' he').trans hbv⟩
  have hU_no_AA : ∀ e ∈ U, ∀ u ∈ A, ∀ w ∈ A, e ∈ G.incidenceSet u → e ∈ G.incidenceSet w →
      u = w := by
    intro e he u hu w hw hiu hiw
    by_contra hne
    have hbu := (hA_bits u hu).1; have hbw := (hA_bits w hw).1
    rcases hiu with rfl | rfl <;> rcases hiw with h2 | h2
    · exact hne h2
    · rw [← h2] at hbw; exact hU_opp e he (hbu.trans hbw.symm)
    · rw [← h2] at hbw; exact hU_opp e he (hbw.trans hbu.symm)
    · exact hne h2
  have hAB_disj : Disjoint A B := disjoint_left.mpr fun v hvA hvB => by
    have h1 := (hA_bits v hvA).1; have h2 := (hB_bits v hvB).1
    exact absurd (h1.symm.trans h2) (by decide)
  have hVP_part : ∀ v : V, v ∈ A ∨ v ∈ B ∨ v ∈ P ∨ v ∈ O := fun v => by
    by_cases ht : touchesU v
    · have h1 := vertexPenalty_le_one G b x v
      have h2 := vertexPenalty_le_one G b y v
      by_cases hx0 : vertexPenalty G b x v = 0
      · exact Or.inl (mem_filter.mpr ⟨mem_univ v, ht, hx0⟩)
      · by_cases hy0 : vertexPenalty G b y v = 0
        · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ v, ht, hy0⟩))
        · exact Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ v, ht, by omega, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (mem_filter.mpr ⟨mem_univ v, ht⟩)))
  have hcost_x : anchoredCost G b x =
      (∑ v ∈ O, vertexPenalty G b x v) + P.card + B.card := by
    have hpB : ∀ v ∈ B, vertexPenalty G b x v = 1 := fun v hvB => by
      have ⟨e, heU, hev⟩ := (mem_filter.mp hvB).2.1
      have hbv := (hB_bits v hvB).1
      exact vertexPenalty_of_not_forall G (by
        push Not; exact ⟨e, hev, by rw [(mem_filter.mp heU).2.1, hbv]; decide⟩)
    have hsum_all : (∑ v : V, vertexPenalty G b x v) =
        (∑ v ∈ A, vertexPenalty G b x v) + (∑ v ∈ B, vertexPenalty G b x v) +
          (∑ v ∈ P, vertexPenalty G b x v) + (∑ v ∈ O, vertexPenalty G b x v) := by
      have hAB : Disjoint A B := hAB_disj
      have hAP : Disjoint A P := disjoint_left.mpr fun v h1 h2 => by
        have := (mem_filter.mp h1).2.2; have := (mem_filter.mp h2).2.2.1; omega
      have hBP : Disjoint B P := disjoint_left.mpr fun v h1 h2 => by
        have := (mem_filter.mp h1).2.2; have := (mem_filter.mp h2).2.2.2; omega
      have hAO : Disjoint A O := disjoint_left.mpr fun v h1 h2 =>
        (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
      have hBO : Disjoint B O := disjoint_left.mpr fun v h1 h2 =>
        (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
      have hPO : Disjoint P O := disjoint_left.mpr fun v h1 h2 =>
        (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
      have huniv : univ = (((A ∪ B) ∪ P) ∪ O) := by
        ext v; simp only [mem_univ, mem_union, true_iff]; have := hVP_part v; tauto
      rw [huniv, sum_union (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hAO, hBO⟩, hPO⟩),
        sum_union (disjoint_union_left.mpr ⟨hAP, hBP⟩), sum_union hAB]
    simp only [anchoredCost, hsum_all]
    have hA0 : ∑ v ∈ A, vertexPenalty G b x v = 0 :=
      sum_eq_zero fun v hv => (mem_filter.mp hv).2.2
    have hB1 : ∑ v ∈ B, vertexPenalty G b x v = B.card := by
      rw [sum_congr rfl fun v hv => hpB v hv, sum_const, smul_eq_mul, mul_one]
    have hP1 : ∑ v ∈ P, vertexPenalty G b x v = P.card := by
      rw [sum_congr rfl fun v hv => (mem_filter.mp hv).2.2.1, sum_const, smul_eq_mul, mul_one]
    omega
  -- B-neighbors of `a ∈ A` across edges in `U`.
  let nbrB (a : V) : Finset V := B.filter fun w =>
    ∃ e ∈ U, e ∈ G.incidenceSet a ∧ e ∈ G.incidenceSet w
  -- Verify Hall's condition from optimality of `y`.
  have hHall : ∀ S : Finset V, S ⊆ A → S.card ≤ (S.biUnion nbrB).card := by
    intro S hSA
    let y' : E → Bool := fun e =>
      if e ∈ U ∧ (G.src e ∈ S ∨ G.tgt e ∈ S) then false else y e
    have hlo := crossingCover_le_anchoredCost G b y'
    rw [← hym] at hlo
    have hA_cost_y : ∀ v ∈ A, vertexPenalty G b y v = 1 := fun v hvA => by
      have ⟨e, heU, hev⟩ := (mem_filter.mp hvA).2.1
      have hbv := (hA_bits v hvA).1
      exact vertexPenalty_of_not_forall G (by
        push Not; exact ⟨e, hev, by rw [(mem_filter.mp heU).2.2, hbv]; decide⟩)
    have hdiff : ∀ v : V,
        (vertexPenalty G b y' v : ℤ) - (vertexPenalty G b y v : ℤ) ≤
          (if v ∈ S.biUnion nbrB then 1 else 0) - (if v ∈ S then 1 else 0) := by
      intro v
      by_cases hvS : v ∈ S
      · have hnot : v ∉ S.biUnion nbrB := fun h => by
          obtain ⟨_, _, hwB⟩ := mem_biUnion.mp h
          exact disjoint_left.mp hAB_disj (hSA hvS) (mem_filter.mp hwB).1
        have hpen0 : vertexPenalty G b y' v = 0 := by
          refine vertexPenalty_of_forall G fun e he => ?_
          have hbv := (hA_bits v (hSA hvS)).1
          rw [hbv]; dsimp [y']
          by_cases heU : e ∈ U
          · have hinc : G.src e ∈ S ∨ G.tgt e ∈ S := by
              rcases he with rfl | rfl
              · exact Or.inl hvS
              · exact Or.inr hvS
            simp [heU, hinc]
          · simp only [heU, false_and, ↓reduceIte]
            have hxf := (hA_bits v (hSA hvS)).2 e he
            cases hy1 : y e
            · rfl
            · exact (heU (mem_filter.mpr ⟨mem_univ e, hxf, hy1⟩)).elim
        rw [hpen0, hA_cost_y v (hSA hvS)]
        simp [hnot, hvS]
      · by_cases hvN : v ∈ S.biUnion nbrB
        · have := vertexPenalty_le_one G b y' v
          simp only [hvN, ↓reduceIte, hvS]; omega
        · simp only [hvN, ↓reduceIte, hvS, sub_zero]
          suffices vertexPenalty G b y' v ≤ vertexPenalty G b y v by omega
          by_cases hpen : vertexPenalty G b y v = 0
          · have hagree : ∀ e, e ∈ G.incidenceSet v → y' e = y e := fun e he => by
              dsimp [y']; split_ifs with hcond
              · exfalso
                rcases hcond with ⟨heU, hS'⟩
                have htv : touchesU v := ⟨e, heU, he⟩
                have hvB : v ∈ B := mem_filter.mpr ⟨mem_univ v, htv, hpen⟩
                rcases hS' with hs | ht
                · exact hvN (mem_biUnion.mpr ⟨G.src e, hs, mem_filter.mpr
                    ⟨hvB, e, heU, Or.inl rfl, he⟩⟩)
                · exact hvN (mem_biUnion.mpr ⟨G.tgt e, ht, mem_filter.mpr
                    ⟨hvB, e, heU, Or.inr rfl, he⟩⟩)
              · rfl
            have hall : ∀ e, e ∈ G.incidenceSet v → y e = b v := by
              by_contra h
              exact absurd ((vertexPenalty_of_not_forall G h).symm.trans hpen) (by decide)
            rw [hpen, vertexPenalty_of_forall G fun e he => (hagree e he).trans (hall e he)]
          · have h1 := vertexPenalty_le_one G b y' v; omega
    have hsum_le : ∑ v : V, ((vertexPenalty G b y' v : ℤ) - (vertexPenalty G b y v : ℤ)) ≤
        ∑ v : V, ((if v ∈ S.biUnion nbrB then (1 : ℤ) else 0) -
          (if v ∈ S then 1 else 0)) := sum_le_sum fun v _ => hdiff v
    have hsum1 : ∑ v : V, (if v ∈ S.biUnion nbrB then (1 : ℤ) else 0) = (S.biUnion nbrB).card := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter, univ_inter]
    have hsum2 : ∑ v : V, (if v ∈ S then (1 : ℤ) else 0) = S.card := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter, univ_inter]
    have hnat1 : ∑ v : V, (vertexPenalty G b y' v : ℤ) = (anchoredCost G b y' : ℤ) := by
      simp only [anchoredCost]; induction (univ : Finset V) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [sum_insert ha, ih]
    have hnat2 : ∑ v : V, (vertexPenalty G b y v : ℤ) = (anchoredCost G b y : ℤ) := by
      simp only [anchoredCost]; induction (univ : Finset V) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [sum_insert ha, ih]
    rw [sum_sub_distrib, sum_sub_distrib, hsum1, hsum2, hnat1, hnat2] at hsum_le
    omega
  obtain ⟨matchB, hinj, hmem_m⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun a : A => nbrB a.1)).mp fun s => by
      have hs := hHall (s.image Subtype.val) fun v hv => by
        obtain ⟨a, _, rfl⟩ := mem_image.mp hv; exact a.2
      rwa [card_image_of_injective s Subtype.coe_injective, image_biUnion] at hs
  -- Partition `A` into `Afull` (no fixed edge at `a`) and `A'` (at least one fixed edge at `a`).
  let incU (a : V) : Finset E := U.filter fun e => e ∈ G.incidenceSet a
  let Afull : Finset V := A.filter fun a => ∀ e, e ∈ G.incidenceSet a → e ∈ U
  let A' : Finset V := A.filter fun a => ¬(∀ e, e ∈ G.incidenceSet a → e ∈ U)
  have hA'_deg : ∀ a ∈ A', (incU a).card ≤ 2 := fun a ha => by
    have hne_imp := (mem_filter.mp ha).2
    push Not at hne_imp
    obtain ⟨e₀, he₀, he₀U⟩ := hne_imp
    have hsub : ((insert e₀ (incU a) : Finset E) : Set E) ⊆ G.incidenceSet a := by
      intro e he
      rcases mem_insert.mp (Finset.mem_coe.mp he) with rfl | he'
      · exact he₀
      · exact (mem_filter.mp he').2
    have hle : (insert e₀ (incU a)).card ≤ (G.incidenceSet a).ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub
    have hne : e₀ ∉ incU a := fun h => he₀U (mem_filter.mp h).1
    rw [card_insert_of_notMem hne] at hle
    have hmax := hd a; omega
  have hnbr_deg : ∀ a ∈ A', (nbrB a).card ≤ 2 := fun a ha => by
    have hsub : nbrB a ⊆ (incU a).image (G.otherEnd a) := fun w hw => by
      obtain ⟨_, e, heU, hea, hew⟩ := mem_filter.mp hw
      have hne : w ≠ a := fun h => disjoint_left.mp hAB_disj (mem_filter.mp ha).1
        (h ▸ (mem_filter.mp hw).1)
      refine mem_image.mpr ⟨e, mem_filter.mpr ⟨heU, hea⟩, ?_⟩
      rcases hea with rfl | rfl <;> rcases hew with h1 | h1
      · exact (hne h1.symm).elim
      · simp [Multigraph.otherEnd, h1]
      · simp [Multigraph.otherEnd, h1, hne]
      · exact (hne h1.symm).elim
    exact (card_le_card hsub).trans (card_image_le.trans (hA'_deg a ha))
  -- Apply `exists_block_peeling_order` to `(A', B)`.
  obtain ⟨ordA', hndA', hmemA', hpeel⟩ := exists_block_peeling_order nbrB (A'.card + B.card)
    A' B (fun a => if h : a ∈ A then matchB ⟨a, h⟩ else a) rfl
    (fun a ha => ⟨fun w hw => (mem_filter.mp hw).1, hnbr_deg a ha⟩)
    (fun a ha => by
      have haA : a ∈ A := (mem_filter.mp ha).1
      simp only [haA, ↓reduceDIte]; exact hmem_m ⟨a, haA⟩)
    (fun a₁ ha₁ a₂ ha₂ heq => by
      have h1 : a₁ ∈ A := (mem_filter.mp ha₁).1
      have h2 : a₂ ∈ A := (mem_filter.mp ha₂).1
      simp only [h1, h2, ↓reduceDIte] at heq
      exact congrArg Subtype.val (hinj heq))
  -- Build the three phases of the edge list `l = l1 ++ l2 ++ l3`.
  let U1 : Finset E := U.filter fun e => ∀ a ∈ A, e ∉ G.incidenceSet a
  let l1 : List E := U1.toList
  let l2 : List E := Afull.toList.flatMap fun a => (incU a).toList
  let l3 : List E := ordA'.flatMap fun a => (incU a).toList
  have hdisj_inc : ∀ a₁ a₂ : V, a₁ ∈ A → a₂ ∈ A → a₁ ≠ a₂ →
      Disjoint (incU a₁) (incU a₂) := fun a₁ a₂ h1 h2 hne =>
    disjoint_left.mpr fun e he1 he2 =>
      hne (hU_no_AA e (mem_filter.mp he1).1 a₁ h1 a₂ h2
        (mem_filter.mp he1).2 (mem_filter.mp he2).2)
  have hl1_nd : l1.Nodup := nodup_toList U1
  have hl2_nd : l2.Nodup := List.nodup_flatMap.mpr
    ⟨fun a _ => nodup_toList (incU a),
      (nodup_toList Afull).pairwise_of_forall_ne fun a₁ h1 a₂ h2 hne =>
      List.disjoint_iff_ne.mpr fun e₁ he₁ e₂ he₂ heq =>
        disjoint_left.mp (hdisj_inc a₁ a₂ (mem_filter.mp (mem_toList.mp h1)).1
          (mem_filter.mp (mem_toList.mp h2)).1 hne)
          (mem_toList.mp he₁) (heq ▸ mem_toList.mp he₂)⟩
  have hl3_nd : l3.Nodup := List.nodup_flatMap.mpr
    ⟨fun a _ => nodup_toList (incU a), hndA'.pairwise_of_forall_ne fun a₁ h1 a₂ h2 hne =>
      List.disjoint_iff_ne.mpr fun e₁ he₁ e₂ he₂ heq =>
        disjoint_left.mp (hdisj_inc a₁ a₂ (mem_filter.mp ((hmemA' a₁).mp h1)).1
          (mem_filter.mp ((hmemA' a₂).mp h2)).1 hne)
          (mem_toList.mp he₁) (heq ▸ mem_toList.mp he₂)⟩
  have hmem_l : ∀ e, e ∈ l1 ++ l2 ++ l3 ↔ e ∈ U := by
    intro e
    simp only [l1, l2, l3, List.mem_append, mem_toList, List.mem_flatMap, hmemA']
    constructor
    · rintro ((h1 | ⟨_, _, h2⟩) | ⟨_, _, h3⟩)
      · exact (mem_filter.mp h1).1
      · exact (mem_filter.mp h2).1
      · exact (mem_filter.mp h3).1
    · intro heU
      by_cases hA : ∃ a ∈ A, e ∈ G.incidenceSet a
      · obtain ⟨a, haA, hea⟩ := hA
        by_cases hfull : ∀ e', e' ∈ G.incidenceSet a → e' ∈ U
        · left; right; exact ⟨a, mem_filter.mpr ⟨haA, hfull⟩, mem_filter.mpr ⟨heU, hea⟩⟩
        · right; exact ⟨a, mem_filter.mpr ⟨haA, hfull⟩, mem_filter.mpr ⟨heU, hea⟩⟩
      · push Not at hA; left; left; exact mem_filter.mpr ⟨heU, hA⟩
  have hdisj12 : List.Disjoint l1 l2 := fun e h1 h2 => by
    obtain ⟨_, hnoA⟩ := mem_filter.mp (mem_toList.mp h1)
    obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp h2
    exact hnoA a (mem_filter.mp (mem_toList.mp ha)).1 (mem_filter.mp (mem_toList.mp he)).2
  have hdisj13 : List.Disjoint l1 l3 := fun e h1 h3 => by
    obtain ⟨_, hnoA⟩ := mem_filter.mp (mem_toList.mp h1)
    obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp h3
    exact hnoA a (mem_filter.mp ((hmemA' a).mp ha)).1 (mem_filter.mp (mem_toList.mp he)).2
  have hdisj23 : List.Disjoint l2 l3 := fun e h2 h3 => by
    obtain ⟨a₁, ha₁, he₁⟩ := List.mem_flatMap.mp h2
    obtain ⟨a₂, ha₂, he₂⟩ := List.mem_flatMap.mp h3
    have hfull := (mem_filter.mp (mem_toList.mp ha₁)).2
    have hnfull := (mem_filter.mp ((hmemA' a₂).mp ha₂)).2
    have hneq : a₁ ≠ a₂ := fun h => hnfull (h ▸ hfull)
    exact disjoint_left.mp (hdisj_inc a₁ a₂ (mem_filter.mp (mem_toList.mp ha₁)).1
      (mem_filter.mp ((hmemA' a₂).mp ha₂)).1 hneq) (mem_toList.mp he₁) (mem_toList.mp he₂)
  have hnd_all : (l1 ++ l2 ++ l3).Nodup :=
    (hl1_nd.append hl2_nd hdisj12).append hl3_nd fun e h12 h3 => by
      rcases List.mem_append.mp h12 with h1 | h2
      · exact hdisj13 h1 h3
      · exact hdisj23 h2 h3
  refine ⟨l1 ++ l2 ++ l3, hnd_all, fun e => (hmem_l e).trans (hU_mem e), ?_⟩
  -- Auxiliary vertex sum bound for any `t ⊆ U`.
  have hsum_O : ∀ l' : List E, (∀ e ∈ l', e ∈ U) →
      ∑ v ∈ O, edgeSplit G (flipPrefix x l') v ≤ ∑ v ∈ O, vertexPenalty G b x v := by
    intro l' hl'
    refine sum_le_sum fun v hvO => ?_
    have hagree : ∀ e, e ∈ G.incidenceSet v → flipPrefix x l' e = x e := fun e he => by
      simp only [flipPrefix]
      by_cases hmem : e ∈ l'
      · exfalso; exact (mem_filter.mp hvO).2 ⟨e, hl' e hmem, he⟩
      · simp [hmem]
    calc edgeSplit G (flipPrefix x l') v
        = edgeSplit G x v := by
          simp only [edgeSplit]; congr 1; apply propext
          exact or_congr (forall₂_congr fun e he => by rw [hagree e he])
            (forall₂_congr fun e he => by rw [hagree e he])
      _ ≤ vertexPenalty G b x v := edgeSplit_le_vertexPenalty G b x v
  have hsplit_all (z : E → Bool) :
      splitCost G z = (∑ v ∈ Afull, edgeSplit G z v) + (∑ v ∈ A', edgeSplit G z v) +
        (∑ v ∈ B, edgeSplit G z v) + (∑ v ∈ P, edgeSplit G z v) +
        (∑ v ∈ O, edgeSplit G z v) := by
    have hAB : Disjoint A B := hAB_disj
    have hAP : Disjoint A P := disjoint_left.mpr fun v h1 h2 => by
      have := (mem_filter.mp h1).2.2; have := (mem_filter.mp h2).2.2.1; omega
    have hBP : Disjoint B P := disjoint_left.mpr fun v h1 h2 => by
      have := (mem_filter.mp h1).2.2; have := (mem_filter.mp h2).2.2.2; omega
    have hAO : Disjoint A O := disjoint_left.mpr fun v h1 h2 =>
      (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
    have hBO : Disjoint B O := disjoint_left.mpr fun v h1 h2 =>
      (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
    have hPO : Disjoint P O := disjoint_left.mpr fun v h1 h2 =>
      (mem_filter.mp h2).2 (mem_filter.mp h1).2.1
    have hAff : Disjoint Afull A' := disjoint_left.mpr fun v h1 h2 =>
      (mem_filter.mp h2).2 (mem_filter.mp h1).2
    have hAu : A = Afull ∪ A' := by
      ext v; simp only [Afull, A', mem_union, mem_filter]; tauto
    have huniv : univ = (((A ∪ B) ∪ P) ∪ O) := by
      ext v; simp only [mem_univ, mem_union, true_iff]; have := hVP_part v; tauto
    simp only [splitCost]
    rw [huniv, sum_union (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hAO, hBO⟩, hPO⟩),
      sum_union (disjoint_union_left.mpr ⟨hAP, hBP⟩), sum_union hAB, hAu, sum_union hAff]
  have hA_zero_of_none (v : V) (hvA : v ∈ A) (l' : List E)
      (hnone : ∀ e ∈ incU v, e ∉ l') (hl'U : ∀ e ∈ l', e ∈ U) :
      edgeSplit G (flipPrefix x l') v = 0 :=
    edgeSplit_of_all_eq G (Or.inl fun e he => by
      have hxf := (hA_bits v hvA).2 e he
      have hel : e ∉ l' := fun h => hnone e (mem_filter.mpr ⟨hl'U e h, he⟩) h
      simp [flipPrefix, hxf, hel])
  have hAfull_zero_of_all (v : V) (hvF : v ∈ Afull) (l' : List E)
      (hall : ∀ e ∈ incU v, e ∈ l') :
      edgeSplit G (flipPrefix x l') v = 0 :=
    edgeSplit_of_all_eq G (Or.inr fun e he => by
      have heU := (mem_filter.mp hvF).2 e he
      simp [flipPrefix, hall e (mem_filter.mpr ⟨heU, he⟩)])
  have hP_le (z : E → Bool) : ∑ v ∈ P, edgeSplit G z v ≤ P.card := by
    calc ∑ v ∈ P, edgeSplit G z v ≤ ∑ _v ∈ P, 1 := sum_le_sum fun v _ => edgeSplit_le_one G z v
      _ = P.card := by simp
  have hB_le (z : E → Bool) : ∑ v ∈ B, edgeSplit G z v ≤ B.card := by
    calc ∑ v ∈ B, edgeSplit G z v ≤ ∑ _v ∈ B, 1 := sum_le_sum fun v _ => edgeSplit_le_one G z v
      _ = B.card := by simp
  intro k hk
  set pre := (l1 ++ l2 ++ l3).take k
  have hpreU : ∀ e ∈ pre, e ∈ U := fun e he => (hmem_l e).mp (List.mem_of_mem_take he)
  rw [hsplit_all (flipPrefix x pre), hcost_x]
  have hO := hsum_O pre hpreU
  have hP := hP_le (flipPrefix x pre)
  by_cases h1 : k ≤ l1.length
  · -- Phase 1: only `l1` edges are flipped; no `A`-vertex touched.
    have hpre_l1 : ∀ e ∈ pre, e ∈ l1 := fun e he => by
      have hte : pre = l1.take k := by
        simp only [pre, List.append_assoc]
        exact List.take_append_of_le_length h1
      exact List.mem_of_mem_take (hte ▸ he)
    have hzeroA : ∀ v ∈ A, edgeSplit G (flipPrefix x pre) v = 0 := fun v hv =>
      hA_zero_of_none v hv pre (fun e he hmem =>
        (mem_filter.mp (mem_toList.mp (hpre_l1 e hmem))).2 v hv (mem_filter.mp he).2) hpreU
    have hAf : ∑ v ∈ Afull, edgeSplit G (flipPrefix x pre) v = 0 :=
      sum_eq_zero fun v hv => hzeroA v (mem_filter.mp hv).1
    have hAp : ∑ v ∈ A', edgeSplit G (flipPrefix x pre) v = 0 :=
      sum_eq_zero fun v hv => hzeroA v (mem_filter.mp hv).1
    have hB := hB_le (flipPrefix x pre)
    omega
  · by_cases h2 : k ≤ (l1 ++ l2).length
    · -- Phase 2: inside `l2` (`Afull` blocks). At most one `a ∈ Afull` is partially flipped.
      have hpre_eq : pre = l1 ++ l2.take (k - l1.length) := by
        simp only [pre]
        rw [List.take_append_of_le_length h2, List.take_append,
          List.take_of_length_le (by omega)]
      have hzeroA' : ∀ v ∈ A', edgeSplit G (flipPrefix x pre) v = 0 := fun v hv =>
        hA_zero_of_none v (mem_filter.mp hv).1 pre (fun e he hmem => by
          rw [hpre_eq] at hmem
          rcases List.mem_append.mp hmem with hm1 | hm2
          · exact (mem_filter.mp (mem_toList.mp hm1)).2 v (mem_filter.mp hv).1
              (mem_filter.mp he).2
          · exact hdisj23 (List.mem_of_mem_take hm2) (List.mem_flatMap.mpr
              ⟨v, (hmemA' v).mpr hv, mem_toList.mpr he⟩)) hpreU
      have hAf_le : ∑ v ∈ Afull, edgeSplit G (flipPrefix x pre) v ≤ 1 := by
        set r2 := k - l1.length
        have hr2 : r2 ≤ l2.length := by simp only [List.length_append] at h2; omega
        obtain ⟨j, hj_le, hj_done, hj_extra⟩ := flatMap_take_prefix_decomp
          (f := fun a : V => (incU a).toList) Afull.toList r2 hr2
        let extra : Finset V := (Afull.toList.take (j + 1) \ Afull.toList.take j).toFinset
        have hdrop : ∀ a ∈ Afull, a ∈ Afull.toList.take j →
            edgeSplit G (flipPrefix x pre) a = 0 := fun a ha haj =>
          hAfull_zero_of_all a ha pre fun e he => by
            rw [hpre_eq]; exact List.mem_append_right _ (hj_done a haj e (mem_toList.mpr he))
        have hunstarted : ∀ a ∈ Afull, a ∉ Afull.toList.take (j + 1) →
            edgeSplit G (flipPrefix x pre) a = 0 := fun a ha hna =>
          hA_zero_of_none a (mem_filter.mp ha).1 pre (fun e he hm => by
            rw [hpre_eq] at hm
            rcases List.mem_append.mp hm with hm1 | hm2
            · exact (mem_filter.mp (mem_toList.mp hm1)).2 a (mem_filter.mp ha).1
                (mem_filter.mp he).2
            · obtain ⟨a', ha', he'⟩ := hj_extra e hm2
              have heqa : a' = a := by
                by_contra hne
                exact disjoint_left.mp (hdisj_inc a' a
                  (mem_filter.mp (mem_toList.mp (List.mem_of_mem_take ha'))).1
                  (mem_filter.mp ha).1 hne) (mem_toList.mp he') he
              exact hna (heqa ▸ ha')) hpreU
        by_cases hjlt : j < Afull.toList.length
        · let a₀ := Afull.toList[j]
          have ha₀_mem : a₀ ∈ Afull := mem_toList.mp (List.getElem_mem hjlt)
          rw [← add_sum_erase _ _ ha₀_mem]
          have hrest0 : ∑ a ∈ Afull.erase a₀, edgeSplit G (flipPrefix x pre) a = 0 := by
            refine sum_eq_zero fun a ha => ?_
            have haA : a ∈ Afull := erase_subset _ _ ha
            have hne : a ≠ a₀ := (mem_erase.mp ha).1
            by_cases htake : a ∈ Afull.toList.take j
            · exact hdrop a haA htake
            · refine hunstarted a haA fun hm => ?_
              rw [List.take_add_one, List.getElem?_eq_getElem hjlt, Option.toList_some,
                List.mem_append, List.mem_singleton] at hm
              exact hm.elim htake hne
          rw [hrest0, add_zero]; exact edgeSplit_le_one G _ a₀
        · have hjeq : Afull.toList.take j = Afull.toList :=
            List.take_of_length_le (by omega)
          rw [sum_eq_zero fun a ha => hdrop a ha (by rw [hjeq]; exact mem_toList.mpr ha)]
          exact Nat.zero_le 1
      have hAp : ∑ v ∈ A', edgeSplit G (flipPrefix x pre) v = 0 :=
        sum_eq_zero fun v hv => hzeroA' v hv
      have hB := hB_le (flipPrefix x pre)
      omega
    · -- Phase 3: inside `l3` (`ordA'` blocks). Apply peeling bound `hpeel`!
      have hpre_eq : pre = (l1 ++ l2) ++ l3.take (k - (l1 ++ l2).length) := by
        simp only [pre]
        rw [List.take_append, List.take_of_length_le (by omega)]
      have hAf0 : ∑ v ∈ Afull, edgeSplit G (flipPrefix x pre) v = 0 :=
        sum_eq_zero fun v hv => hAfull_zero_of_all v hv pre fun e he => by
          rw [hpre_eq]; exact List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨v, mem_toList.mpr hv, mem_toList.mpr he⟩))
      set r := k - (l1 ++ l2).length
      have hlen_l3 : r ≤ l3.length := by
        have hlen := hk
        rw [List.length_append] at hlen
        omega
      obtain ⟨j, hj_le, hj_done, hj_extra⟩ := flatMap_take_prefix_decomp
        (f := fun a : V => (incU a).toList) ordA' r hlen_l3
      -- Every `b ∈ finishedIn nbrB A' B (ordA'.take j)` has all incident edges in `pre`.
      have hB_fin : ∀ w ∈ finishedIn nbrB A' B (ordA'.take j),
          edgeSplit G (flipPrefix x pre) w = 0 := by
        intro w hw
        have hw' : w ∈ B ∧ ∀ a ∈ A', w ∈ nbrB a → a ∈ ordA'.take j := by
          simpa [finishedIn] using hw
        have hwB : w ∈ B := hw'.1
        refine edgeSplit_of_all_eq G (Or.inr fun e he => ?_)
        by_cases hxe : x e = true
        · simp [flipPrefix, hxe]
        · have heU : e ∈ U := mem_filter.mpr ⟨mem_univ e, Bool.eq_false_iff.mpr hxe,
            (hB_bits w hwB).2 e he⟩
          simp only [flipPrefix, decide_eq_true_eq, Bool.or_eq_true]
          right
          by_cases hA : ∃ a ∈ A, e ∈ G.incidenceSet a
          · obtain ⟨a, haA, hea⟩ := hA
            by_cases hfull : ∀ e', e' ∈ G.incidenceSet a → e' ∈ U
            · rw [hpre_eq]; exact List.mem_append_left _ (List.mem_append_right _
                (List.mem_flatMap.mpr ⟨a, mem_toList.mpr (mem_filter.mpr ⟨haA, hfull⟩),
                  mem_toList.mpr (mem_filter.mpr ⟨heU, hea⟩)⟩))
            · have haA' : a ∈ A' := mem_filter.mpr ⟨haA, hfull⟩
              have hwa : w ∈ nbrB a := mem_filter.mpr ⟨hwB, e, heU, hea, he⟩
              have haj : a ∈ ordA'.take j := hw'.2 a haA' hwa
              rw [hpre_eq]; exact List.mem_append_right _ (hj_done a haj e
                (mem_toList.mpr (mem_filter.mpr ⟨heU, hea⟩)))
          · push Not at hA
            rw [hpre_eq]; exact List.mem_append_left _ (List.mem_append_left _
              (mem_toList.mpr (mem_filter.mpr ⟨heU, hA⟩)))
      let finB := finishedIn nbrB A' B (ordA'.take j)
      have hfin_sub : finB ⊆ B := fun w hw => by
        have hw' : w ∈ B ∧ ∀ a ∈ A', w ∈ nbrB a → a ∈ ordA'.take j := by
          simpa [finB, finishedIn] using hw
        exact hw'.1
      have hB_split : ∑ w ∈ B, edgeSplit G (flipPrefix x pre) w ≤ B.card - finB.card := by
        rw [← sum_sdiff hfin_sub, sum_eq_zero hB_fin, add_zero]
        calc ∑ w ∈ B \ finB, edgeSplit G (flipPrefix x pre) w
            ≤ ∑ _w ∈ B \ finB, 1 := sum_le_sum fun w _ => edgeSplit_le_one G _ w
          _ = (B \ finB).card := by simp
          _ = B.card - finB.card := card_sdiff_of_subset hfin_sub
      -- Started `A'` vertices are contained in `ordA'.take (min (j + 1) ordA'.length)`.
      have hA'_split : ∑ a ∈ A', edgeSplit G (flipPrefix x pre) a ≤ j + 1 := by
        let started : Finset V := (ordA'.take (j + 1)).toFinset
        have hzero : ∀ a ∈ A', a ∉ started → edgeSplit G (flipPrefix x pre) a = 0 := by
          intro a ha hns
          refine hA_zero_of_none a (mem_filter.mp ha).1 pre (fun e he hm => ?_) hpreU
          rw [hpre_eq] at hm
          rcases List.mem_append.mp hm with hm12 | hm3
          · rcases List.mem_append.mp hm12 with hm1 | hm2
            · exact (mem_filter.mp (mem_toList.mp hm1)).2 a (mem_filter.mp ha).1
                (mem_filter.mp he).2
            · exact hdisj23 hm2 (List.mem_flatMap.mpr ⟨a, (hmemA' a).mpr ha, mem_toList.mpr he⟩)
          · obtain ⟨a', ha', he'⟩ := hj_extra e hm3
            have heqa : a' = a := by
              by_contra hne
              have ha'A' : a' ∈ A' := (hmemA' a').mp (List.mem_of_mem_take ha')
              exact disjoint_left.mp (hdisj_inc a' a (mem_filter.mp ha'A').1
                (mem_filter.mp ha).1 hne) (mem_toList.mp he') he
            exact hns (List.mem_toFinset.mpr (heqa ▸ ha'))
        calc ∑ a ∈ A', edgeSplit G (flipPrefix x pre) a
            = ∑ a ∈ A' ∩ started, edgeSplit G (flipPrefix x pre) a := by
              symm; refine sum_subset inter_subset_left fun a ha hna => hzero a ha fun hs =>
                hna (mem_inter.mpr ⟨ha, hs⟩)
          _ ≤ (A' ∩ started).card := by
              calc _ ≤ ∑ _a ∈ A' ∩ started, 1 :=
                      sum_le_sum fun a _ => edgeSplit_le_one G _ a
                _ = _ := by simp
          _ ≤ started.card := card_le_card inter_subset_right
          _ ≤ (ordA'.take (j + 1)).length := List.toFinset_card_le _
          _ ≤ j + 1 := List.length_take_le _ _
      have hj_bd : j ≤ finB.card + 1 := hpeel j hj_le
      have hfin_le : finB.card ≤ B.card := card_le_card hfin_sub
      omega

/-- Between consecutive vertex bipartitions `b` and `c = update b v true`, flipping first the
edges that become `true–true` under `c` and then interpolating to `leastClampedMinimizer G c`
yields a monotone edge chain with every prefix split cost at most `crossingCover G b + 3`. -/
private theorem exists_step_flip_chain [DecidableEq V] (hd : G.MaxDegreeLE 3)
    (b : V → Bool) (v : V) :
    let c : V → Bool := update b v true
    let x := leastClampedMinimizer G b
    let y := leastClampedMinimizer G c
    ∃ l : List E, l.Nodup ∧ (∀ e, e ∈ l ↔ x e = false ∧ y e = true) ∧
      ∀ k ≤ l.length, splitCost G (flipPrefix x (l.take k)) ≤ crossingCover G b + 3 := by
  have := Fintype.ofFinite E
  intro c x y
  have hbc : b ≤ c := fun w => by
    by_cases hw : w = v
    · subst hw; simp [c]
    · simp [c, hw]
  have hxy : x ≤ y := leastClampedMinimizer_mono G hbc
  have hx_cl : IsClamped G b x := isClamped_leastClampedMinimizer G b
  have hy_cl : IsClamped G c y := isClamped_leastClampedMinimizer G c
  have hxm : anchoredCost G b x = crossingCover G b := anchoredCost_leastClampedMinimizer G b
  have hym : anchoredCost G c y = crossingCover G c := anchoredCost_leastClampedMinimizer G c
  -- Phase A: flip the edges that are `false` in `x` and join two `true` vertices in `c`.
  let F : Finset E := univ.filter fun e => x e = false ∧ c (G.src e) = true ∧ c (G.tgt e) = true
  let lF : List E := F.toList
  have hF_in_y : ∀ e ∈ F, y e = true := fun e he => by
    have ⟨_, hs, ht⟩ := (mem_filter.mp he).2
    have := (isClamped_iff_eq G c y).mp hy_cl e (hs.trans ht.symm)
    exact this.trans hs
  have hflip_le : ∀ l' : List E, (∀ e ∈ l', e ∈ F) →
      anchoredCost G c (flipPrefix x l') ≤ anchoredCost G c x := by
    intro l'
    induction l' with
    | nil => intro _; simp
    | cons e rest ih =>
      intro hmem
      have heF : e ∈ F := hmem e List.mem_cons_self
      have hrest : ∀ e' ∈ rest, e' ∈ F := fun e' he' => hmem e' (List.mem_cons_of_mem e he')
      have he_eq : c (G.src e) = c (G.tgt e) :=
        (mem_filter.mp heF).2.2.1.trans (mem_filter.mp heF).2.2.2.symm
      have he_src : c (G.src e) = true := (mem_filter.mp heF).2.2.1
      have hupd : flipPrefix x (e :: rest) = update (flipPrefix x rest) e (c (G.src e)) := by
        ext e'
        by_cases h : e' = e
        · subst h; simp [flipPrefix, he_src]
        · simp [flipPrefix, h]
      rw [hupd]
      exact (anchoredCost_update_same_le G c (flipPrefix x rest) e he_eq).trans (ih hrest)
  let z := flipPrefix x lF
  have hzy : z ≤ y := fun e => by
    by_cases hmem : e ∈ lF
    · have heF : e ∈ F := mem_toList.mp hmem
      simp [z, flipPrefix, hmem, hF_in_y e heF]
    · simp only [z, flipPrefix, hmem, decide_false, Bool.or_false]; exact hxy e
  have hz_cl : IsClamped G c z := by
    rw [isClamped_iff_eq]
    intro e heq
    cases hs : c (G.src e)
    · have hbs : b (G.src e) = false := le_antisymm (hs ▸ hbc (G.src e)) (Bool.false_le _)
      have hbt : b (G.tgt e) = false :=
        le_antisymm ((hs ▸ heq.symm) ▸ hbc (G.tgt e)) (Bool.false_le _)
      have hxe : x e = false :=
        ((isClamped_iff_eq G b x).mp hx_cl e (hbs.trans hbt.symm)).trans hbs
      have hnot : e ∉ lF := fun h => by
        have := (mem_filter.mp (mem_toList.mp h)).2.2.1
        exact absurd (hs.symm.trans this) (by decide)
      simp [z, flipPrefix, hxe, hnot]
    · have ht : c (G.tgt e) = true := heq.symm.trans hs
      by_cases hxe : x e = true
      · simp [z, flipPrefix, hxe]
      · have hmem : e ∈ lF :=
          mem_toList.mpr (mem_filter.mpr ⟨mem_univ e, Bool.eq_false_iff.mpr hxe, hs, ht⟩)
        simp [z, flipPrefix, hmem]
  have hcost_z : anchoredCost G c z ≤ crossingCover G b + 1 := by
    calc anchoredCost G c z ≤ anchoredCost G c x := hflip_le lF fun e he => mem_toList.mp he
      _ ≤ anchoredCost G b x + 1 := anchoredCost_update_le G b x v true
      _ = crossingCover G b + 1 := by rw [hxm]
  obtain ⟨l2, hl2_nd, hl2_mem, hl2_bd⟩ := exists_clamped_flip_chain G hd hz_cl hy_cl hym
  have hdisj : List.Disjoint lF l2 := fun e h1 h2 => by
    have hze := ((hl2_mem e).mp h2).1
    have : z e = true := by simp [z, flipPrefix, h1]
    exact absurd (this.symm.trans hze) (by decide)
  refine ⟨lF ++ l2, (nodup_toList F).append hl2_nd hdisj, ?_, ?_⟩
  · intro e
    rw [List.mem_append, mem_toList, hl2_mem]
    constructor
    · rintro (hF | ⟨hzf, hyt⟩)
      · exact ⟨(mem_filter.mp hF).2.1, hF_in_y e hF⟩
      · have : x e = false := by
          cases hxe : x e
          · rfl
          · have hzt : z e = true := by simp [z, flipPrefix, hxe]
            exact absurd (hzt.symm.trans hzf) (by decide)
        exact ⟨this, hyt⟩
    · rintro ⟨hxf, hyt⟩
      by_cases hF : e ∈ F
      · exact Or.inl hF
      · right; refine ⟨?_, hyt⟩
        have hnot : e ∉ lF := fun h => hF (mem_toList.mp h)
        simp [z, flipPrefix, hxf, hnot]
  · intro k hk
    by_cases h1 : k ≤ lF.length
    · have htake : (lF ++ l2).take k = lF.take k := List.take_append_of_le_length h1
      rw [htake]
      have hcost : anchoredCost G c (flipPrefix x (lF.take k)) ≤ crossingCover G b + 1 :=
        (hflip_le _ fun e he => mem_toList.mp (List.mem_of_mem_take he)).trans
          ((anchoredCost_update_le G b x v true).trans (by rw [hxm]))
      exact (splitCost_le_anchoredCost G c _).trans (hcost.trans (by omega))
    · have htake : (lF ++ l2).take k = lF ++ l2.take (k - lF.length) := by
        rw [List.take_append, List.take_of_length_le (by omega)]
      rw [htake]
      have hfp : flipPrefix x (lF ++ l2.take (k - lF.length)) =
          flipPrefix z (l2.take (k - lF.length)) := by
        ext e; simp [z, flipPrefix, Bool.or_assoc]
      rw [hfp]
      have hlen2 : k - lF.length ≤ l2.length := by
        rw [List.length_append] at hk; omega
      exact (hl2_bd (k - lF.length) hlen2).trans (by omega)

/-- **Global edge ordering with split cost bounded by `M + 3`.** Given any vertex list
`vs : List V` covering `V`, concatenating the canonical monotone flip chains yields a nodup list
`es : List E` covering `E` such that every prefix has `splitCost` at most `M + 3`, where `M`
bounds `crossingCover G` on every vertex prefix of `vs`. -/
theorem exists_edge_order_splitCost_le [DecidableEq V] (hd : G.MaxDegreeLE 3)
    (vs : List V) (hvs : ∀ v : V, v ∈ vs) (M : ℕ)
    (hM : ∀ i ≤ vs.length, crossingCover G (fun v => decide (v ∈ vs.take i)) ≤ M) :
    ∃ es : List E, es.Nodup ∧ (∀ e : E, e ∈ es) ∧
      ∀ k ≤ es.length, splitCost G (fun e => decide (e ∈ es.take k)) ≤ M + 3 := by
  have := Fintype.ofFinite E
  have hchain : ∀ m : ℕ, m ≤ vs.length →
      let bm : V → Bool := fun v => decide (v ∈ vs.take m)
      ∃ es : List E, es.Nodup ∧
        (∀ e : E, e ∈ es ↔ leastClampedMinimizer G bm e = true) ∧
        ∀ k ≤ es.length, splitCost G (fun e => decide (e ∈ es.take k)) ≤ M + 3 := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨[], List.nodup_nil, fun e => ?_, fun k hk => ?_⟩
      · have hb0 : (fun _ : V => decide (false = true)) = (fun _ => false) := rfl
        have hlc := leastClampedMinimizer_const G false
        simp only [List.take_zero, List.not_mem_nil, decide_false, List.not_mem_nil, false_iff]
        rw [show leastClampedMinimizer G (fun _ => false) e = false from congrFun hlc e]
        decide
      · have : k = 0 := by simpa using hk
        subst this
        have : splitCost G (fun _ => false) = 0 := sum_eq_zero fun v _ => by
          simp [edgeSplit]
        simp [this]
    | succ m ih =>
      intro hm
      have hmlt : m < vs.length := by omega
      obtain ⟨es, hnd, hmem, hbd⟩ := ih (by omega)
      set b : V → Bool := fun v => decide (v ∈ vs.take m)
      set u := vs[m]
      have hstep_b : (fun v => decide (v ∈ vs.take (m + 1))) = update b u true := by
        ext v
        have hmem_t : v ∈ vs.take (m + 1) ↔ v ∈ vs.take m ∨ v = u := by
          rw [List.take_add_one, List.getElem?_eq_getElem hmlt, Option.toList_some,
            List.mem_append, List.mem_singleton]
        by_cases hv : v = u
        · subst hv; simp [hmem_t]
        · simp [b, hv, hmem_t]
      obtain ⟨l, hl_nd, hl_mem, hl_bd⟩ := exists_step_flip_chain G hd b u
      have hdisj : List.Disjoint es l := fun e h1 h2 => by
        have h1' := (hmem e).mp h1
        have h2' := ((hl_mem e).mp h2).1
        exact absurd (h1'.symm.trans h2') (by decide)
      refine ⟨es ++ l, hnd.append hl_nd hdisj, ?_, ?_⟩
      · intro e
        rw [hstep_b, List.mem_append, hmem, hl_mem]
        have hmono : leastClampedMinimizer G b e ≤ leastClampedMinimizer G (update b u true) e :=
          leastClampedMinimizer_mono G (fun w => by
            by_cases hw : w = u
            · subst hw; simp
            · rw [update_of_ne hw]) e
        cases hx : leastClampedMinimizer G b e <;>
          cases hy : leastClampedMinimizer G (update b u true) e <;>
          simp_all [Bool.le_iff_imp]
      · intro k hk
        by_cases h1 : k ≤ es.length
        · rw [List.take_append_of_le_length h1]; exact hbd k h1
        · rw [List.take_append, List.take_of_length_le (by omega)]
          have heq_f : (fun e => decide (e ∈ es ++ l.take (k - es.length))) =
              flipPrefix (leastClampedMinimizer G b) (l.take (k - es.length)) := by
            ext e
            simp only [flipPrefix, List.mem_append]
            by_cases h1e : e ∈ es <;> by_cases h2e : e ∈ l.take (k - es.length)
            · simp [h1e, h2e, (hmem e).mp h1e]
            · simp [h1e, h2e, (hmem e).mp h1e]
            · have hf : leastClampedMinimizer G b e = false := by
                cases h : leastClampedMinimizer G b e
                · rfl
                · exact (h1e ((hmem e).mpr h)).elim
              simp [h1e, h2e, hf]
            · have hf : leastClampedMinimizer G b e = false := by
                cases h : leastClampedMinimizer G b e
                · rfl
                · exact (h1e ((hmem e).mpr h)).elim
              simp [h1e, h2e, hf]
          rw [heq_f]
          have hlenl : k - es.length ≤ l.length := by rw [List.length_append] at hk; omega
          exact (hl_bd (k - es.length) hlenl).trans (Nat.add_le_add_right (hM m (by omega)) 3)
  obtain ⟨es, hnd, hmem, hbd⟩ := hchain vs.length le_rfl
  refine ⟨es, hnd, fun e => (hmem e).mpr ?_, hbd⟩
  have hb_top : (fun v => decide (v ∈ vs.take vs.length)) = fun _ => true := by
    ext v; simp [hvs v]
  rw [hb_top, leastClampedMinimizer_const]

omit [Fintype V] [DecidableEq E] in
/-- **Cubic cutwidth is at most maximum crossing-cover size plus six.** Given any vertex ordering
`vs : List V` of a finite loopless cubic multigraph `G`, if `crossingCover G` is at most `M` on
every prefix of `vs`, then `G` admits a layout of width at most `M + 6`. -/
theorem exists_width_le_max_crossingCover [Finite V] [DecidableEq V]
    (h3 : ∀ v : V, (G.incidenceSet v).ncard = 3)
    (vs : List V) (hvs : ∀ v : V, v ∈ vs) (M : ℕ)
    (hM : ∀ i ≤ vs.length,
      open Classical in crossingCover G (fun v => decide (v ∈ vs.take i)) ≤ M) :
    ∃ π : Layout V, (G.width π : ℝ) ≤ M + 6 := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  have hd : G.MaxDegreeLE 3 := fun v => (h3 v).le
  have hM' : ∀ i ≤ vs.length, crossingCover G (fun v => decide (v ∈ vs.take i)) ≤ M := by
    intro i hi; convert hM i hi
  obtain ⟨es, hnd, hmem, hbd⟩ := exists_edge_order_splitCost_le G hd vs hvs M hM'
  let score : E → ℝ := fun e => (es.idxOf e : ℝ)
  have hlt_len : ∀ e : E, es.idxOf e < es.length := fun e => List.idxOf_lt_length_of_mem (hmem e)
  refine G.exists_width_le_of_edgeScore h3 score (a := 0) (δ := 1) zero_lt_one es.length
    (B := (M : ℝ) + 6) ?_ ?_ ?_
  · have : {e : E | score e < 0} = ∅ := Set.eq_empty_of_forall_notMem fun e h => by
      have : (0 : ℝ) ≤ (es.idxOf e : ℝ) := Nat.cast_nonneg _
      have h' : (es.idxOf e : ℝ) < 0 := h; linarith
    rw [this, Set.ncard_empty]
    simp only [Nat.cast_zero, mul_zero]; positivity
  · have : {e : E | 0 + (es.length : ℝ) * 1 ≤ score e} = ∅ :=
      Set.eq_empty_of_forall_notMem fun e h => by
        have hlt : (es.idxOf e : ℝ) < (es.length : ℝ) := by exact_mod_cast hlt_len e
        have h' : 0 + (es.length : ℝ) * 1 ≤ (es.idxOf e : ℝ) := h; linarith
    rw [this, Set.ncard_empty]
    simp only [Nat.cast_zero, mul_zero]; positivity
  · intro i hi
    have hwin : {e : E | (0 : ℝ) + i * 1 ≤ score e ∧ score e < 0 + ((i : ℝ) + 1) * 1} ⊆
        {es[i]} := by
      intro e ⟨hlo, hhi⟩
      have hlo' : (i : ℝ) ≤ (es.idxOf e : ℝ) := by simpa [score] using hlo
      have hhi' : (es.idxOf e : ℝ) < ((i + 1 : ℕ) : ℝ) := by
        push_cast; simpa [score] using hhi
      have hidx : es.idxOf e = i := by
        have h1 : i ≤ es.idxOf e := by exact_mod_cast hlo'
        have h2 : es.idxOf e < i + 1 := by exact_mod_cast hhi'
        omega
      rw [Set.mem_singleton_iff, ← List.getElem_idxOf (hlt_len e)]
      simp [hidx]
    have hwin_card : {e : E | (0 : ℝ) + i * 1 ≤ score e ∧
        score e < 0 + ((i : ℝ) + 1) * 1}.ncard ≤ 1 :=
      (Set.ncard_le_ncard hwin).trans (by simp)
    have hstr_iff : ∀ v : V, G.EdgeStraddles score (0 + (i : ℝ) * 1) v ↔
        edgeSplit G (fun e => decide (e ∈ es.take i)) v = 1 := by
      intro v
      have hmem_take : ∀ e : E, e ∈ es.take i ↔ es.idxOf e < i := fun e => by
        constructor
        · intro he
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
          have hj_i : j < i := by rw [List.length_take] at hj; omega
          have hj_lt : j < es.length := by omega
          rw [List.getElem_take, hnd.idxOf_getElem j hj_lt]
          exact hj_i
        · intro hlt
          have hge := List.getElem_idxOf (hlt_len e)
          have hmt : es.idxOf e < (es.take i).length := by rw [List.length_take]; omega
          have := List.getElem_mem hmt
          rwa [List.getElem_take, hge] at this
      have hcast : ∀ e : E, ((es.idxOf e : ℝ) < i) ↔ (es.idxOf e < i) := fun e => by
        exact_mod_cast Iff.rfl
      constructor
      · rintro ⟨e₁, he₁, hlt, e₂, he₂, hge⟩
        have h1 : e₁ ∈ es.take i := (hmem_take e₁).mpr ((hcast e₁).mp (by simpa [score] using hlt))
        have h2 : e₂ ∉ es.take i := fun h => by
          have : (es.idxOf e₂ : ℝ) < i := by exact_mod_cast (hmem_take e₂).mp h
          have hge' : (i : ℝ) ≤ (es.idxOf e₂ : ℝ) := by simpa [score] using hge
          linarith
        simp only [edgeSplit]; split_ifs with hall
        · exfalso; rcases hall with hf | ht
          · exact absurd (hf e₁ he₁) (by simp [h1])
          · exact absurd (ht e₂ he₂) (by simp [h2])
        · rfl
      · intro h1
        have hnot : ¬((∀ e, e ∈ G.incidenceSet v → decide (e ∈ es.take i) = false) ∨
            (∀ e, e ∈ G.incidenceSet v → decide (e ∈ es.take i) = true)) := fun h => by
          rw [edgeSplit_of_all_eq G h] at h1; omega
        push Not at hnot
        obtain ⟨⟨e₁, he₁, h1t⟩, ⟨e₂, he₂, h2f⟩⟩ := hnot
        have hm1 : e₁ ∈ es.take i := by by_contra hm; exact h1t (by simp [hm])
        have hm2 : e₂ ∉ es.take i := fun hm => h2f (by simp [hm])
        refine ⟨e₁, he₁, by simpa [score] using (hcast e₁).mpr ((hmem_take e₁).mp hm1),
          e₂, he₂, ?_⟩
        by_contra hlt2
        have hlt2' : (es.idxOf e₂ : ℝ) < i := by simpa [score] using lt_of_not_ge hlt2
        exact hm2 ((hmem_take e₂).mpr ((hcast e₂).mp hlt2'))
    have hstr_card : {v | G.EdgeStraddles score (0 + (i : ℝ) * 1) v}.ncard =
        splitCost G (fun e => decide (e ∈ es.take i)) := by
      have heq_set : {v | G.EdgeStraddles score (0 + (i : ℝ) * 1) v} =
          ((univ.filter fun v => edgeSplit G (fun e => decide (e ∈ es.take i)) v = 1) : Set V) := by
        ext v; exact (hstr_iff v).trans (by simp)
      rw [heq_set, Set.ncard_coe_finset, card_filter]
      refine sum_congr rfl fun v _ => ?_
      have := edgeSplit_le_one G (fun e => decide (e ∈ es.take i)) v
      split_ifs <;> omega
    have hnat : {v | G.EdgeStraddles score (0 + (i : ℝ) * 1) v}.ncard +
        3 * {e : E | (0 : ℝ) + i * 1 ≤ score e ∧ score e < 0 + ((i : ℝ) + 1) * 1}.ncard ≤
        M + 6 := by
      rw [hstr_card]; have := hbd i hi.le; omega
    exact_mod_cast hnat

end Chain

end Cslib.Circuits.Frontier.CrossingCover

