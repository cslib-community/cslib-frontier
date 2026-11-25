/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Internal horizontal-section column-pairing combinatorics

Internal partition of row-section active columns into consecutive pairs and odd leftover columns
(`activeRows`, `pairedCols`, `oddCols`, `sectionPeers`) shared by `BlockCols`, `AdditiveBound`,
`StageParts`, `StageStep`, and `UpperBound`; never re-exported through `Zhegalkin`.

## Main definitions

* `Cslib.Circuits.blockIndices`, `activeRows`, `pairedCols`, `oddCols`, `sectionPeers`:
  horizontal-section blocks and column-pairing partition.

## Main results

* `Cslib.Circuits.sum_filter_hasCol_eq`, `two_mul_sum_card_pairedCols_le`,
  `sum_card_oddCols_le`: monoid partition identity and double-counting bounds.
-/

public section

open Finset

namespace Cslib.Circuits

theorem div_lt_ceilDiv {j m p : ℕ} (hj : j < m) (hp : 0 < p) :
    j / p < m ⌈/⌉ p :=
  (Nat.div_lt_iff_lt_mul hp).mpr <| by
    rw [mul_comm]
    exact lt_of_lt_of_le hj ((ceilDiv_le_iff_le_smul hp).mp le_rfl)

/-- Block `q` of width `width` in `Fin k`. -/
@[expose] def blockIndices (k width q : ℕ) : Finset (Fin k) :=
  univ.filter fun j : Fin k => j.1 / width = q

theorem sum_card_blockIndices (k width : ℕ) (hw : 0 < width) :
    ∑ q ∈ range (k ⌈/⌉ width), #(blockIndices k width q) = k := by
  simpa only [blockIndices, card_univ, Fintype.card_fin] using
    (card_eq_sum_card_fiberwise (s := univ) (t := range (k ⌈/⌉ width))
      (f := fun j : Fin k => j.1 / width) fun j _ =>
        mem_range.mpr (div_lt_ceilDiv j.isLt hw)).symm

theorem card_blockIndices_le (k width q : ℕ) (hw : 0 < width) :
    #(blockIndices k width q) ≤ width := by
  have hinj : Set.InjOn (fun j : Fin k => (⟨j.1 % width, Nat.mod_lt _ hw⟩ : Fin width))
      (blockIndices k width q) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hq₁ : j₁.1 / width = q := (mem_filter.mp hj₁).2
    have hq₂ : j₂.1 / width = q := (mem_filter.mp hj₂).2
    have hm : j₁.1 % width = j₂.1 % width := congrArg Fin.val heq
    apply Fin.ext
    rw [← Nat.div_add_mod j₁.1 width, ← Nat.div_add_mod j₂.1 width, hq₁, hq₂, hm]
  exact (card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj).trans_eq (by simp)


section SectionPairing

/-- Horizontal section index and peer row pair `(u, (r₁, r₂))`. -/
abbrev SectionPeer (m : ℕ) := ℕ × (Fin m × Fin m)

/-- Horizontal section index `u` of a section-peer tuple. -/
abbrev SectionPeer.sec {m : ℕ} (up : SectionPeer m) : ℕ := up.1

/-- First row index `r₁` of a section-peer tuple. -/
abbrev SectionPeer.row₁ {m : ℕ} (up : SectionPeer m) : Fin m := up.2.1

/-- Second row index `r₂` of a section-peer tuple. -/
abbrev SectionPeer.row₂ {m : ℕ} (up : SectionPeer m) : Fin m := up.2.2

variable {Col : Type*} [Fintype Col] {m : ℕ}

/-- Rows in horizontal section `u` that have `true` in column `c`. -/
@[expose] def activeRows (hasCol : Fin m → Col → Bool) (p u : ℕ) (c : Col) : Finset (Fin m) :=
  univ.filter fun r : Fin m => r.1 / p = u ∧ hasCol r c = true

/-- Columns in which rows `r₁ < r₂` of section `u` form one of the consecutive pairs of `1`s. -/
@[expose] def pairedCols (hasCol : Fin m → Col → Bool) (p u : ℕ) (r₁ r₂ : Fin m) : Finset Col :=
  univ.filter fun c : Col =>
    ∃ t : Fin (#(activeRows hasCol p u c) / 2),
      (activeRows hasCol p u c).orderEmbOfFin rfl
        ⟨2 * t.1, by have := t.isLt; omega⟩ = r₁ ∧
      (activeRows hasCol p u c).orderEmbOfFin rfl
        ⟨2 * t.1 + 1, by have := t.isLt; omega⟩ = r₂

/-- Columns in which row `r` is the unique unpaired leftover `1` in its section `r.1 / p`. -/
@[expose] def oddCols (hasCol : Fin m → Col → Bool) (p : ℕ) (r : Fin m) : Finset Col :=
  univ.filter fun c : Col =>
    ∃ h : 2 * (#(activeRows hasCol p (r.1 / p) c) / 2) < #(activeRows hasCol p (r.1 / p) c),
      (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl
        ⟨2 * (#(activeRows hasCol p (r.1 / p) c) / 2), h⟩ = r

theorem mem_pairedCols_imp {hasCol : Fin m → Col → Bool} {p u : ℕ} {r₁ r₂ : Fin m}
    {c : Col} (hc : c ∈ pairedCols hasCol p u r₁ r₂) :
    r₁ < r₂ ∧ r₁.1 / p = u ∧ r₂.1 / p = u ∧ hasCol r₁ c = true ∧ hasCol r₂ c = true := by
  unfold pairedCols at hc
  rw [mem_filter] at hc
  obtain ⟨_, t, hr₁, hr₂⟩ := hc
  let S := activeRows hasCol p u c
  have ht_lt : t.1 < #S / 2 := t.isLt
  have hlt : (⟨2 * t.1, by omega⟩ : Fin #S) < ⟨2 * t.1 + 1, by omega⟩ := by simp
  have hord : r₁ < r₂ := hr₁ ▸ hr₂ ▸ (S.orderEmbOfFin rfl).strictMono hlt
  have hm₁ : r₁ ∈ S := hr₁ ▸ S.orderEmbOfFin_mem rfl _
  have hm₂ : r₂ ∈ S := hr₂ ▸ S.orderEmbOfFin_mem rfl _
  obtain ⟨_, hu₁, hc₁⟩ := mem_filter.mp hm₁
  obtain ⟨_, hu₂, hc₂⟩ := mem_filter.mp hm₂
  exact ⟨hord, hu₁, hu₂, hc₁, hc₂⟩

theorem mem_oddCols_imp {hasCol : Fin m → Col → Bool} {p : ℕ} {r : Fin m} {c : Col}
    (hc : c ∈ oddCols hasCol p r) : hasCol r c = true := by
  obtain ⟨_, h, hr⟩ := mem_filter.mp hc
  set S := activeRows hasCol p (r.1 / p) c
  have hm : S.orderEmbOfFin rfl ⟨2 * (#S / 2), h⟩ ∈ S := S.orderEmbOfFin_mem rfl _
  rw [hr] at hm
  exact (mem_filter.mp hm).2.2

/-- Other rows in the same horizontal section of height `p` as row `r`. -/
@[expose] def sectionPeers (p : ℕ) (r : Fin m) : Finset (Fin m) :=
  univ.filter fun r' : Fin m => r'.1 / p = r.1 / p ∧ r' ≠ r

theorem card_sectionPeers_le {p : ℕ} (hp : 0 < p) (r : Fin m) :
    #(sectionPeers p r) ≤ p - 1 := by
  have hpeers_eq : sectionPeers p r = (blockIndices m p (r.1 / p)).erase r := by
    ext r'
    simp only [sectionPeers, blockIndices, mem_filter, mem_univ, true_and, mem_erase]
    tauto
  have hr_mem : r ∈ blockIndices m p (r.1 / p) := mem_filter.mpr ⟨mem_univ r, rfl⟩
  rw [hpeers_eq, card_erase_of_mem hr_mem]
  exact Nat.sub_le_sub_right (card_blockIndices_le m p (r.1 / p) hp) 1

/-- Every row's active columns partition into its paired columns with peers in the same section and
its odd-leftover columns. This holds in any additive commutative monoid, without cancellation. -/
theorem sum_filter_hasCol_eq {G : Type*} [AddCommMonoid G]
    (hasCol : Fin m → Col → Bool) (p : ℕ) (val : Col → G) (r : Fin m) :
    (∑ c with hasCol r c = true, val c) =
      (∑ r' ∈ sectionPeers p r,
        ∑ c ∈ pairedCols hasCol p (r.1 / p) (min r r') (max r r'), val c) +
      ∑ c ∈ oddCols hasCol p r, val c := by
  classical
  let peerSet (r' : Fin m) : Finset Col :=
    pairedCols hasCol p (r.1 / p) (min r r') (max r r')
  -- `r` is the smaller or the larger row of every pair it belongs to.
  have hr (r' : Fin m) : min r r' = r ∨ max r r' = r :=
    (le_total r r').imp min_eq_left max_eq_left
  -- Rows of the sorted active rows of a column determine their positions.
  have hpos {c : Col} {i j : ℕ} {hi : i < #(activeRows hasCol p (r.1 / p) c)}
      {hj : j < #(activeRows hasCol p (r.1 / p) c)}
      (h : (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl ⟨i, hi⟩ =
        (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl ⟨j, hj⟩) : i = j :=
    congrArg Fin.val (((activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl).injective h)
  have hdisj_peers : (sectionPeers p r : Set (Fin m)).PairwiseDisjoint peerSet := by
    intro r₁ _ r₂ _ hne
    refine Finset.disjoint_left.mpr fun c hc₁ hc₂ => hne ?_
    obtain ⟨_, t₁, ha₁, hb₁⟩ := mem_filter.mp hc₁
    obtain ⟨_, t₂, ha₂, hb₂⟩ := mem_filter.mp hc₂
    obtain rfl : t₁ = t₂ := by
      rcases (hr r₁).imp ha₁.trans hb₁.trans with e₁ | e₁ <;>
        rcases (hr r₂).imp ha₂.trans hb₂.trans with e₂ | e₂ <;>
        exact Fin.ext (by have := hpos (e₁.trans e₂.symm); omega)
    have h₁ := congrArg Fin.val (ha₁.symm.trans ha₂)
    have h₂ := congrArg Fin.val (hb₁.symm.trans hb₂)
    simp only [Fin.val_min, Fin.val_max] at h₁ h₂
    exact Fin.ext (by omega)
  have hdisj_odd : Disjoint ((sectionPeers p r).biUnion peerSet) (oddCols hasCol p r) := by
    refine Finset.disjoint_left.mpr fun c hc hodd => ?_
    obtain ⟨r', _, hc⟩ := mem_biUnion.mp hc
    obtain ⟨_, t, ha, hb⟩ := mem_filter.mp hc
    obtain ⟨_, _, he⟩ := mem_filter.mp hodd
    have := t.isLt
    rcases (hr r').imp ha.trans hb.trans with e | e <;> have := hpos (e.trans he.symm) <;> omega
  rw [← sum_biUnion hdisj_peers, ← sum_union hdisj_odd]
  refine sum_congr (ext fun c => ?_) fun _ _ => rfl
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_biUnion]
  refine ⟨fun hc => ?_, ?_⟩
  · set S := activeRows hasCol p (r.1 / p) c
    let emb := S.orderEmbOfFin rfl
    obtain ⟨idx, hidx⟩ : r ∈ Set.range emb := by
      rw [range_orderEmbOfFin]
      exact mem_filter.mpr ⟨mem_univ r, rfl, hc⟩
    have := idx.isLt
    by_cases hlt : idx.1 < 2 * (#S / 2)
    · -- `r` is paired with the other row `emb j` of its consecutive pair of active rows.
      let j : Fin #S := ⟨4 * (idx.1 / 2) + 1 - idx.1, by omega⟩
      have hj : idx.1 ≠ j.1 := by dsimp only [j]; omega
      have h₀ : 2 * (idx.1 / 2) < #S := by omega
      have h₁ : 2 * (idx.1 / 2) + 1 < #S := by omega
      have hmin : emb ⟨_, h₀⟩ = min r (emb j) := by
        rw [← hidx, ← emb.monotone.map_min]
        exact congrArg emb (Fin.ext (by simp only [j, Fin.val_min]; omega))
      have hmax : emb ⟨_, h₁⟩ = max r (emb j) := by
        rw [← hidx, ← emb.monotone.map_max]
        exact congrArg emb (Fin.ext (by simp only [j, Fin.val_max]; omega))
      exact Or.inl ⟨emb j, mem_filter.mpr ⟨mem_univ _,
        (mem_filter.mp (S.orderEmbOfFin_mem rfl j)).2.1,
        fun h => hj (congrArg Fin.val (emb.injective (hidx.trans h.symm)))⟩,
        mem_filter.mpr ⟨mem_univ c, (⟨idx.1 / 2, by omega⟩ : Fin (#S / 2)), hmin, hmax⟩⟩
    · have hodd : 2 * (#S / 2) < #S := by omega
      exact Or.inr (mem_filter.mpr ⟨mem_univ c, hodd,
        (congrArg emb (Fin.ext (by omega : 2 * (#S / 2) = idx.1) :
          (⟨_, hodd⟩ : Fin #S) = idx)).trans hidx⟩)
  · rintro (⟨r', -, hc⟩ | hc)
    · obtain ⟨-, -, -, hc₁, hc₂⟩ := mem_pairedCols_imp hc
      exact (hr r').elim (· ▸ hc₁) (· ▸ hc₂)
    · exact mem_oddCols_imp hc

/-- Twice the total number of paired columns across all sections is at most the weight of
`hasCol`. -/
theorem two_mul_sum_card_pairedCols_le (hasCol : Fin m → Col → Bool) {p : ℕ} (hp : 0 < p) :
    2 * (∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m,
      #(pairedCols hasCol p u pair.1 pair.2)) ≤
      ∑ r : Fin m, #{c : Col | hasCol r c = true} := by
  classical
  have hsec_sum (u : ℕ) :
      ∑ pair : Fin m × Fin m, #(pairedCols hasCol p u pair.1 pair.2) =
        ∑ c : Col, #(activeRows hasCol p u c) / 2 := by
    simp only [pairedCols, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    set S := activeRows hasCol p u c
    let f : Fin (#S / 2) → Fin m × Fin m := fun t =>
      (S.orderEmbOfFin rfl ⟨2 * t.1, by have := t.isLt; omega⟩,
        S.orderEmbOfFin rfl ⟨2 * t.1 + 1, by have := t.isLt; omega⟩)
    have hf_inj : Function.Injective f := by
      intro t₁ t₂ heq
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Fin.val ((S.orderEmbOfFin rfl).injective h₁)
      exact Fin.ext (by dsimp at h₂; omega)
    have hcard_img : #(univ.image f) = #S / 2 := by
      rw [card_image_of_injective _ hf_inj, card_univ, Fintype.card_fin]
    have hsum_img :
        (∑ pair : Fin m × Fin m,
          if ∃ t : Fin (#S / 2),
            S.orderEmbOfFin rfl ⟨2 * t.1, by have := t.isLt; omega⟩ = pair.1 ∧
            S.orderEmbOfFin rfl ⟨2 * t.1 + 1, by have := t.isLt; omega⟩ = pair.2
          then 1 else 0) = #(univ.image f) := by
      rw [sum_boole, Nat.cast_id]
      congr 1
      ext ⟨r₁, r₂⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, f, Prod.mk.injEq]
    exact hsum_img.trans hcard_img
  calc 2 * ∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m, #(pairedCols hasCol p u pair.1 pair.2)
      = 2 * ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, #(activeRows hasCol p u c) / 2 := by
        congr 1
        exact sum_congr rfl fun u _ => hsec_sum u
    _ = ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, 2 * (#(activeRows hasCol p u c) / 2) := by
        rw [mul_sum]
        exact sum_congr rfl fun u _ => mul_sum _ _ _
    _ ≤ ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, #(activeRows hasCol p u c) :=
        sum_le_sum fun u _ => sum_le_sum fun c _ => Nat.mul_div_le _ 2
    _ = ∑ c : Col, ∑ u ∈ range (m ⌈/⌉ p), #(activeRows hasCol p u c) := sum_comm
    _ = ∑ c : Col, #{r : Fin m | hasCol r c = true} := by
        refine sum_congr rfl fun c _ => ?_
        have hpart := card_eq_sum_card_fiberwise
          (s := univ.filter fun r : Fin m => hasCol r c = true)
          (t := range (m ⌈/⌉ p)) (f := fun r : Fin m => r.1 / p)
          fun r _ => mem_range.mpr (div_lt_ceilDiv r.isLt hp)
        rw [hpart]
        refine sum_congr rfl fun u _ => congrArg card ?_
        ext r
        simp only [activeRows, mem_filter, mem_univ, true_and]
        tauto
    _ = ∑ r : Fin m, #{c : Col | hasCol r c = true} := by
        simp only [card_filter]
        exact sum_comm

/-- The total number of odd-leftover columns across all rows is at most `(m ⌈/⌉ p) * |Col|`. -/
theorem sum_card_oddCols_le (hasCol : Fin m → Col → Bool) {p : ℕ} (hp : 0 < p) :
    (∑ r : Fin m, #(oddCols hasCol p r)) ≤ (m ⌈/⌉ p) * Fintype.card Col := by
  rw [← sum_fiberwise_of_maps_to (t := range (m ⌈/⌉ p))
    fun r _ => mem_range.mpr (div_lt_ceilDiv r.isLt hp)]
  calc ∑ u ∈ range (m ⌈/⌉ p),
        ∑ r ∈ univ.filter (fun r : Fin m => r.1 / p = u), #(oddCols hasCol p r)
      ≤ ∑ _u ∈ range (m ⌈/⌉ p), Fintype.card Col := by
        refine sum_le_sum fun u _ => ?_
        simp only [oddCols, card_filter]
        rw [sum_comm]
        calc ∑ c : Col, ∑ r ∈ univ.filter (fun r : Fin m => r.1 / p = u),
              (if ∃ h : 2 * (#(activeRows hasCol p (r.1 / p) c) / 2) <
                  #(activeRows hasCol p (r.1 / p) c),
                (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl ⟨_, h⟩ = r then 1 else 0)
            ≤ ∑ _c : Col, 1 := by
              refine sum_le_sum fun c _ => ?_
              let S := activeRows hasCol p u c
              by_cases hlt : 2 * (#S / 2) < #S
              · let r₀ := S.orderEmbOfFin rfl ⟨2 * (#S / 2), hlt⟩
                have hr₀_sec : r₀.1 / p = u := (mem_filter.mp (S.orderEmbOfFin_mem rfl _)).2.1
                rw [sum_eq_single r₀]
                · simp only [hr₀_sec]
                  split_ifs
                  · exact le_rfl
                  · exact Nat.zero_le 1
                · intro r hr hne
                  have hr_u : r.1 / p = u := (mem_filter.mp hr).2
                  rw [ite_eq_right]
                  rintro ⟨h', heq⟩
                  simp only [hr_u] at h' heq
                  exact hne heq.symm
                · intro habs
                  exact (habs (mem_filter.mpr ⟨mem_univ r₀, hr₀_sec⟩)).elim
              · rw [sum_eq_zero]
                · exact Nat.zero_le 1
                · intro r hr
                  have hr_u : r.1 / p = u := (mem_filter.mp hr).2
                  rw [ite_eq_right]
                  rintro ⟨h', _⟩
                  simp only [hr_u] at h'
                  exact hlt h'
          _ = Fintype.card Col := by simp
    _ = (m ⌈/⌉ p) * Fintype.card Col := by simp

end SectionPairing

end Cslib.Circuits
