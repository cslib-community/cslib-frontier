/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Monotone.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.Sort

/-!
# Change counts, piece counts, and sorted groups

A function has at most `T` changes when every nondecreasing sequence has at most `T`
adjacent positions with unequal outputs, and at most `M` pieces when it is constant on the
level sets of a monotone rank function with values below `M`. Sorting a finite set by a key and
splitting it into consecutive groups yields a large group on which most functions in a finite
family are constant. The key may have ties, and the size bound uses natural-number division.

## Main definitions

* `Cslib.ChangesAtMost`: a uniform bound on changes along nondecreasing sequences.
* `Cslib.PiecesAtMost`: a function constant on the level sets of a monotone rank function with
  values below `M`.

## Main results

* `Cslib.ChangesAtMost.comp_antitone`: antitone precomposition preserves a change bound.
* `Cslib.ChangesAtMost.decide_le`, `Cslib.ChangesAtMost.decide_ge`: threshold predicates on a linear
  order change at most once.
* `Cslib.ChangesAtMost.pi`, `Cslib.ChangesAtMost.finset_pi`: a finite tuple of functions changes at
  most the sum of the coordinate change bounds.
* `Cslib.PiecesAtMost.changesAtMost`: a function with at most `M` pieces changes at most `M - 1`
  times.
* `Cslib.ChangesAtMost.exists_sorted_group`: a group of at least `|P| / G` points,
  with at most `T |Q| / G` exceptional functions.
* `Cslib.ChangesAtMost.length_le_succ_of_isChain`: an alternating sequence along an ordered list has
  bounded length.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*, Threshold/Internal/Changes]
  [Schlesinger2026Algebraic]
-/

public section

namespace Cslib

variable {α β γ : Type*}

/-- Every nondecreasing sequence has at most `T` adjacent changes under `f`. -/
@[expose] def ChangesAtMost [Preorder α] (f : α → β) (T : ℕ) : Prop :=
  ∀ z : ℕ → α, Monotone z → ∀ S : Finset ℕ,
    (∀ i ∈ S, f (z i) ≠ f (z (i + 1))) → S.card ≤ T

/-- Increasing a change bound preserves it. -/
theorem ChangesAtMost.mono [Preorder α] {f : α → β} {T T' : ℕ}
    (h : ChangesAtMost f T) (hT : T ≤ T') : ChangesAtMost f T' :=
  fun z hz S hS => (h z hz S hS).trans hT

/-- Post-composition preserves a change bound. -/
theorem ChangesAtMost.comp [Preorder α] {f : α → β} {T : ℕ}
    (h : ChangesAtMost f T) (g : β → γ) : ChangesAtMost (g ∘ f) T :=
  fun z hz S hS => h z hz S fun i hi heq => hS i hi (congrArg g heq)

/-- Monotone precomposition preserves a change bound. -/
theorem ChangesAtMost.comp_monotone [Preorder α] [Preorder γ] {f : α → β} {T : ℕ}
    (h : ChangesAtMost f T) {g : γ → α} (hg : Monotone g) :
    ChangesAtMost (f ∘ g) T :=
  fun z hz S hS => h (g ∘ z) (hg.comp hz) S hS

/-- Antitone precomposition preserves a change bound. -/
theorem ChangesAtMost.comp_antitone [Preorder α] [Preorder γ] {f : α → β} {T : ℕ}
    (h : ChangesAtMost f T) {g : γ → α} (hg : Antitone g) :
    ChangesAtMost (f ∘ g) T := by
  intro z hz S hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Nat.zero_le T
  set M := S.max' hne + 1
  have hlt : ∀ i ∈ S, i < M := fun i hi => Nat.lt_succ_of_le (S.le_max' i hi)
  have hinj : Set.InjOn (fun i => M - 1 - i) S := fun i hi j hj hij => by
    have := hlt i hi
    have := hlt j hj
    dsimp only at hij
    omega
  rw [← Finset.card_image_of_injOn hinj]
  refine h (fun k => g (z (M - min k M))) (fun _ _ hab => hg (hz (by omega))) _ fun k hk => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  have := hlt i hi
  simpa only [Function.comp_apply, show M - min (M - 1 - i) M = i + 1 by omega,
    show M - min (M - 1 - i + 1) M = i by omega] using (hS i hi).symm

/-- A constant function has no changes. -/
theorem ChangesAtMost.const [Preorder α] (b : β) :
    ChangesAtMost (fun _ : α => b) 0 := fun _ _ S hS => by
  rw [Finset.eq_empty_iff_forall_notMem.mpr fun i hi => hS i hi rfl, Finset.card_empty]

/-- A threshold predicate `decide (θ ≤ ·)` on a linear order changes at most once. -/
theorem ChangesAtMost.decide_le [LinearOrder α] (θ : α) [DecidableRel (· ≤ · : α → α → Prop)] :
    ChangesAtMost (fun u : α => decide (θ ≤ u)) 1 := by
  intro z hz S hS
  have hcut (i : ℕ) (hi : i ∈ S) : z i < θ ∧ θ ≤ z (i + 1) := by
    have hn : ¬ θ ≤ z i := fun hc =>
      hS i hi (by simp only [hc, hc.trans (hz (Nat.le_succ i)), decide_true])
    have hp : θ ≤ z (i + 1) := by
      by_contra hn'
      exact hS i hi (by simp only [hn, hn', decide_false])
    exact ⟨lt_of_not_ge hn, hp⟩
  refine Finset.card_le_one.mpr fun i hi j hj => by_contra fun hne => ?_
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact not_lt_of_ge ((hcut i hi).2.trans (hz (Nat.succ_le_of_lt h))) (hcut j hj).1
  · exact not_lt_of_ge ((hcut j hj).2.trans (hz (Nat.succ_le_of_lt h))) (hcut i hi).1

/-- A threshold predicate `decide (· ≤ θ)` on a linear order changes at most once: it is
`decide_le` in the order dual, precomposed with the antitone `toDual`. -/
theorem ChangesAtMost.decide_ge [LinearOrder α] (θ : α) [DecidableRel (· ≤ · : α → α → Prop)] :
    ChangesAtMost (fun u : α => decide (u ≤ θ)) 1 :=
  (decide_le (α := αᵒᵈ) (OrderDual.toDual θ)).comp_antitone (g := OrderDual.toDual) fun _ _ h => h

/-- A tuple of functions indexed by a finite type changes at most the sum of the individual
change bounds. -/
theorem ChangesAtMost.pi [Preorder α] {ι : Type*} [Fintype ι] {β : ι → Type*}
    {f : (i : ι) → α → β i} {T : ι → ℕ} (hf : ∀ i, ChangesAtMost (f i) (T i)) :
    ChangesAtMost (fun a i => f i a) (∑ i, T i) := by
  classical
  intro z hz S hS
  have hsub : S ⊆ Finset.univ.biUnion fun i => S.filter fun k => f i (z k) ≠ f i (z (k + 1)) :=
    fun k hk => by
      obtain ⟨i, hi⟩ : ∃ i, f i (z k) ≠ f i (z (k + 1)) := by
        by_contra! hno
        exact hS k hk (funext hno)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hk, hi⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun i _ => hf i z hz _ fun _ hk => (Finset.mem_filter.mp hk).2))

/-- A tuple of functions indexed by a finite set changes at most the sum of the individual
change bounds. -/
theorem ChangesAtMost.finset_pi [Preorder α] {ι : Type*} {s : Finset ι} {β : ι → Type*}
    {f : (i : ι) → α → β i} {T : ι → ℕ} (hf : ∀ i ∈ s, ChangesAtMost (f i) (T i)) :
    ChangesAtMost (fun a (i : s) => f i.1 a) (∑ i ∈ s, T i) := by
  rw [← s.sum_attach]
  exact ChangesAtMost.pi fun i => hf i.1 i.2

/-- `Φ` has at most `M` pieces when it is constant on the level sets of a monotone rank
function `π : α → ℕ` with values below `M`. -/
@[expose] def PiecesAtMost [Preorder α] (Φ : α → β) (M : ℕ) : Prop :=
  ∃ π : α → ℕ, Monotone π ∧ (∀ t, π t < M) ∧ ∀ t t', π t = π t' → Φ t = Φ t'

/-- Increasing a piece bound preserves it. -/
theorem PiecesAtMost.mono [Preorder α] {Φ : α → β} {M M' : ℕ}
    (h : PiecesAtMost Φ M) (hM : M ≤ M') : PiecesAtMost Φ M' := by
  obtain ⟨π, mono, lt, fac⟩ := h
  exact ⟨π, mono, fun t => (lt t).trans_le hM, fac⟩

/-- Post-composition preserves a piece bound. -/
theorem PiecesAtMost.comp [Preorder α] {Φ : α → β} {M : ℕ}
    (h : PiecesAtMost Φ M) (g : β → γ) : PiecesAtMost (fun t => g (Φ t)) M := by
  obtain ⟨π, mono, lt, fac⟩ := h
  exact ⟨π, mono, lt, fun t t' e => by simp only [fac t t' e]⟩

/-- A function with at most `M` pieces changes at most `M - 1` times. -/
theorem PiecesAtMost.changesAtMost [Preorder α] {Φ : α → β} {M : ℕ}
    (h : PiecesAtMost Φ M) : ChangesAtMost Φ (M - 1) := by
  obtain ⟨π, mono, lt, fac⟩ := h
  intro z hz S hS
  have key : ∀ i ∈ S, π (z i) < π (z (i + 1)) := fun i hi =>
    (mono (hz (Nat.le_succ i))).lt_or_eq.resolve_right fun he => hS i hi (fac _ _ he)
  have inj : Set.InjOn (fun i => π (z (i + 1))) S := fun i hi i' hi' heq => by
    dsimp only at heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := mono (hz (by omega : i + 1 ≤ i'))
      have := key i' hi'
      omega
    · have := mono (hz (by omega : i' + 1 ≤ i))
      have := key i hi
      omega
  simpa only [Nat.card_Ioo, tsub_zero] using Finset.card_le_card_of_injOn
    (t := Finset.Ioo 0 M) (fun i => π (z (i + 1)))
    (fun i hi => by
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      exact ⟨(Nat.zero_le _).trans_lt (key i hi), lt _⟩)
    inj

variable [LinearOrder α]

/-- Without a change in `[a, a + m)`, a sequence is constant on `[a, a + m]`. -/
private theorem eq_of_forall_not_change {s : ℕ → β} {a m : ℕ}
    (h : ∀ c, a ≤ c → c < a + m → s c = s (c + 1)) : ∀ j ≤ m, s (a + j) = s a := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih (by omega), ← Nat.add_assoc]
    exact (h (a + j) (by omega) (by omega)).symm

open scoped Classical in
/-- **Each function is nonconstant on few groups.** Cut the positions into consecutive groups
of `L`. A function with at most `T` changes along the nondecreasing sequence `z` is nonconstant
on at most `T` of the first `G` groups. -/
private theorem card_nonconstant_groups_le {Ψ : α → β} {T : ℕ} (h : ChangesAtMost Ψ T)
    {z : ℕ → α} (hz : Monotone z) (L G : ℕ) :
    ((Finset.range G).filter fun g =>
      ∃ j < L, ∃ j' < L, Ψ (z (g * L + j)) ≠ Ψ (z (g * L + j'))).card ≤ T := by
  classical
  set bad := (Finset.range G).filter fun g =>
    ∃ j < L, ∃ j' < L, Ψ (z (g * L + j)) ≠ Ψ (z (g * L + j'))
  -- Every nonconstant group contains a change position.
  have hchange : ∀ g ∈ bad, ∃ c, g * L ≤ c ∧ c < g * L + L ∧ Ψ (z c) ≠ Ψ (z (c + 1)) :=
    fun g hg => by
      obtain ⟨j, hj, j', hj', hne⟩ := (Finset.mem_filter.mp hg).2
      by_contra! hno
      have hc := eq_of_forall_not_change (s := fun i => Ψ (z i)) (a := g * L) (m := L - 1)
        fun c hc1 hc2 => hno c hc1 (by omega)
      exact hne ((hc j (by omega)).trans (hc j' (by omega)).symm)
  choose! chg hchg using hchange
  have inj : Set.InjOn chg bad := fun g hg g' hg' heq => by
    obtain ⟨a1, a2, -⟩ := hchg g hg
    obtain ⟨b1, b2, -⟩ := hchg g' hg'
    have e1 := Nat.div_eq_of_lt_le a1 (by rw [Nat.succ_mul]; exact a2)
    have e2 := Nat.div_eq_of_lt_le b1 (by rw [Nat.succ_mul]; exact b2)
    rw [← e1, ← e2, heq]
  rw [← Finset.card_image_of_injOn inj]
  exact h z hz _ fun i hi => by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hi
    exact (hchg g hg).2.2

/-- The nondecreasing order of a finite set along a linearly ordered key. -/
private theorem exists_sorted_list {ι : Type*} (P : Finset ι) (key : ι → α) :
    ∃ l : List ι, l.length = P.card ∧ l.Nodup ∧ (∀ a, a ∈ l ↔ a ∈ P) ∧
      ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → key l[i] ≤ key l[j] := by
  let l := P.toList.mergeSort (fun a b => decide (key a ≤ key b))
  have hperm : l.Perm P.toList := List.mergeSort_perm _ _
  have hsorted : l.Pairwise (fun a b => decide (key a ≤ key b) = true) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) _
  refine ⟨l, hperm.length_eq.trans (Finset.length_toList P),
    hperm.nodup_iff.mpr (Finset.nodup_toList P),
    fun a => hperm.mem_iff.trans Finset.mem_toList, fun i j hi hj hij => ?_⟩
  rcases hij.lt_or_eq with h | rfl
  · exact of_decide_eq_true (List.pairwise_iff_getElem.mp hsorted i j hi hj h)
  · exact le_rfl

/-- **Lemma 1 (sorted groups).** If every `Ψ q` with `q ∈ Q` changes at most `T` times, there are
a subset `P'` of `P` with at least `⌊|P| / G⌋` elements and a subset `Qbad` of `Q` with
`G |Qbad| ≤ T |Q|` such that the functions `p ↦ Ψ q (key p)` are constant on `P'` for every
`q ∈ Q` outside `Qbad`. In the proof, `P'` is one of the `G` consecutive groups of `⌊|P| / G⌋`
elements of `P` sorted by `key`. -/
theorem ChangesAtMost.exists_sorted_group {ι κ : Type*} (P : Finset ι) (Q : Finset κ) (key : ι → α)
    (Ψ : κ → α → β) {T G : ℕ} (hG : 0 < G) (hΨ : ∀ q ∈ Q, ChangesAtMost (Ψ q) T) :
    ∃ P' ⊆ P, ∃ Qbad ⊆ Q, P.card / G ≤ P'.card ∧ G * Qbad.card ≤ T * Q.card ∧
      ∀ q ∈ Q, q ∉ Qbad → ∀ p ∈ P', ∀ p' ∈ P', Ψ q (key p) = Ψ q (key p') := by
  classical
  set N := P.card
  set L := N / G
  rcases Nat.eq_zero_or_pos L with hL | hL
  · exact ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, by simp [hL], by simp,
      fun _ _ _ _ hp => (Finset.notMem_empty _ hp).elim⟩
  have hGL : G * L ≤ N := Nat.mul_div_le N G
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos hG hL) hGL
  obtain ⟨l, hlen, hnodup, hmem, hsorted⟩ := exists_sorted_list P key
  let z : ℕ → α := fun i => key (l[min i (N - 1)]'(by omega))
  have hz : Monotone z := fun _ _ hij => hsorted _ _ _ _ (min_le_min_right _ hij)
  -- The `g`-th group and its elements.
  let grp : ℕ → Finset ι := fun g => ((l.drop (g * L)).take L).toFinset
  have hgrp_mem : ∀ g < G, ∀ p ∈ grp g, ∃ j < L, key p = z (g * L + j) := fun g hg p hp => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hp)
    have hjL : j < L := by simp only [List.length_take, List.length_drop] at hj; omega
    have hbd := (Nat.mul_le_mul_right L (by omega : g + 1 ≤ G)).trans hGL
    refine ⟨j, hjL, ?_⟩
    simp only [z, List.getElem_take, List.getElem_drop]
    congr 2
    rw [Nat.add_mul, one_mul] at hbd
    omega
  have hgrp_card : ∀ g < G, (grp g).card = L := fun g hg => by
    rw [List.toFinset_card_of_nodup
      ((hnodup.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _))]
    have hbd := (Nat.mul_le_mul_right L (by omega : g + 1 ≤ G)).trans hGL
    simp only [List.length_take, List.length_drop, hlen]
    rw [Nat.add_mul, one_mul] at hbd
    omega
  -- Bad groups for each function, and double counting.
  let bad : ℕ → κ → Prop := fun g q =>
    ∃ j < L, ∃ j' < L, Ψ q (z (g * L + j)) ≠ Ψ q (z (g * L + j'))
  have hsum : ∑ g ∈ Finset.range G, (Q.filter fun q => bad g q).card ≤ T * Q.card := by
    have hb := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.range G) (t := Q) bad
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hb
    exact hb ▸ (Finset.sum_le_sum fun q hq => card_nonconstant_groups_le (hΨ q hq) hz L G
      ).trans_eq (by rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm])
  obtain ⟨g, hg, hgood⟩ := Finset.exists_le_of_sum_le (s := Finset.range G)
    (f := fun g => G * (Q.filter fun q => bad g q).card) (g := fun _ => T * Q.card)
    ⟨0, Finset.mem_range.mpr hG⟩ (by
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      exact Nat.mul_le_mul_left _ hsum)
  have hgG : g < G := Finset.mem_range.mp hg
  refine ⟨grp g, fun p hp => (hmem p).mp (List.mem_of_mem_drop (List.mem_of_mem_take
    (List.mem_toFinset.mp hp))), Q.filter fun q => bad g q, Finset.filter_subset _ _,
    (hgrp_card g hgG).ge, hgood, fun q hqQ hq p hp p' hp' => ?_⟩
  obtain ⟨j, hj, hpj⟩ := hgrp_mem g hgG p hp
  obtain ⟨j', hj', hpj'⟩ := hgrp_mem g hgG p' hp'
  rw [hpj, hpj']
  exact by_contra fun hne => hq (Finset.mem_filter.mpr ⟨hqQ, j, hj, j', hj', hne⟩)

/-! ### Alternating sequences along ordered lists -/

/-- Any ordered list along which `f` alternates between consecutive elements has length at
most `T + 1` whenever `ChangesAtMost f T`. -/
theorem ChangesAtMost.length_le_succ_of_isChain {α β : Type*} [Preorder α] {f : α → β} {T : ℕ}
    (hf : ChangesAtMost f T) {ts : List α} (hmono : ts.IsChain (· ≤ ·))
    (halt : (ts.map f).IsChain (· ≠ ·)) :
    ts.length ≤ T + 1 := by
  rcases Nat.eq_zero_or_pos ts.length with h0 | hpos
  · omega
  let z : ℕ → α := fun i => ts[min i (ts.length - 1)]'(by omega)
  have hcard := hf z (fun _ _ hij =>
    hmono.sortedLE.getElem_le_getElem_of_le (min_le_min_right _ hij))
    (Finset.range (ts.length - 1)) fun i hi => by
      have hi' : i + 1 < ts.length := by rw [Finset.mem_range] at hi; omega
      have hne := List.isChain_iff_getElem.mp halt i (by simpa only [List.length_map] using hi')
      simp only [List.getElem_map] at hne
      simpa only [z, show min i (ts.length - 1) = i by omega,
        show min (i + 1) (ts.length - 1) = i + 1 by omega] using hne
  rw [Finset.card_range] at hcard
  omega

end Cslib
