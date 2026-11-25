/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-!
# Hypergraph-degeneracy upper bound on upper shadows of down-closed set families

For a down-closed finite family `Δ : Finset (Finset α)` over any ground type `α`, if the `p`-uniform
layer satisfies `p! · #{I ∈ Δ | #I = p} ≤ d ^ p` (`p ≥ 1`), then the total size of all layers of
cardinality at least `p` satisfies

`#{I ∈ Δ | p ≤ #I} ≤ #{I ∈ Δ | #I = 1} ^ (p - 1) · 2 ^ d`

(`Finset.card_filter_card_ge_le`). When `#{I ∈ Δ | #I = 1} ≤ d`, the entire family lives in the
powerset of at most `d` active singletons and has size at most `2 ^ d`; when
`d < #{I ∈ Δ | #I = 1}`, averaging degrees in the `p`-uniform layer finds an active vertex `i₀` of
link degree `deg(i₀)` with `(p - 1)! · deg(i₀) ≤ d ^ (p - 1)`, and decomposing into the deletion
`{I ∈ Δ | i₀ ∉ I}` and link `{J | i₀ ∉ J ∧ insert i₀ J ∈ Δ}` closes by induction on
`(p, #{I ∈ Δ | #I = 1})`.

Unlike real-exponent Kruskal–Katona approximations, this bound holds purely in `ℕ` for all `p ≥ 1`
and all `d : ℕ` without ground-set finiteness or decidability assumptions. This degeneracy shadow
theorem is original to this library;
`CslibFrontier.Computability.Circuit.Frontier.PolynomialWitness` uses it to extract low-degree
monomial pivots from graded-weight footprints.

## Main results

* `Finset.card_filter_card_ge_le`: hypergraph-degeneracy upper bound on `#{I ∈ Δ | p ≤ #I}` for
  down-closed `Finset` families over any type `α`.
-/

public section

namespace Finset

open scoped BigOperators

private theorem card_biUnion_eq_card_singletons {α : Type*} [DecidableEq α] {Γ : Finset (Finset α)}
    (hΓ : ∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Γ → J ∈ Γ) :
    #(Γ.biUnion id) = #{I ∈ Γ | #I = 1} := by
  refine card_bij (fun i _ => ({i} : Finset α))
    (fun i hi => by
      obtain ⟨I, hI, hiI⟩ := mem_biUnion.mp hi
      exact mem_filter.mpr ⟨hΓ (singleton_subset_iff.mpr hiI) hI, card_singleton i⟩)
    (fun _ _ _ _ hij => singleton_injective hij) ?_
  intro I hI
  obtain ⟨hIΓ, h1⟩ := mem_filter.mp hI
  obtain ⟨i, rfl⟩ := card_eq_one.mp h1
  exact ⟨i, mem_biUnion.mpr ⟨{i}, hIΓ, mem_singleton_self i⟩, rfl⟩

private theorem subset_biUnion_powerset {α : Type*} [DecidableEq α] (Γ : Finset (Finset α)) :
    Γ ⊆ (Γ.biUnion id).powerset := fun I hI =>
  mem_powerset.mpr fun _ hi => mem_biUnion.mpr ⟨I, hI, hi⟩

/-- **Hypergraph-degeneracy shadow bound.** Let `Δ` be a down-closed finite family of finite subsets
of `α`. For every `p ≥ 1` and `d : ℕ`, if `p! · #{I ∈ Δ | #I = p} ≤ d ^ p`, then
`#{I ∈ Δ | p ≤ #I} ≤ #{I ∈ Δ | #I = 1} ^ (p - 1) · 2 ^ d`. -/
theorem card_filter_card_ge_le {α : Type*} {p d : ℕ} (hp : 1 ≤ p) {Δ : Finset (Finset α)}
    (hdown : ∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Δ → J ∈ Δ)
    (hcap : p.factorial * #{I ∈ Δ | #I = p} ≤ d ^ p) :
    #{I ∈ Δ | p ≤ #I} ≤ #{I ∈ Δ | #I = 1} ^ (p - 1) * 2 ^ d := by
  classical
  induction p, hp using Nat.le_induction generalizing Δ with
  | base =>
    simp only [Nat.sub_self, pow_zero, one_mul]
    rw [Nat.factorial_one, one_mul, pow_one] at hcap
    have h2 := card_le_card (subset_biUnion_powerset Δ)
    rw [card_powerset, card_biUnion_eq_card_singletons hdown] at h2
    exact (card_filter_le _ _).trans (h2.trans (Nat.pow_le_pow_right two_pos hcap))
  | succ q hq ih_p =>
    simp only [Nat.add_sub_cancel]
    suffices ∀ v (Γ : Finset (Finset α)),
        (∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Γ → J ∈ Γ) →
        (q + 1).factorial * #{I ∈ Γ | #I = q + 1} ≤ d ^ (q + 1) →
        #{I ∈ Γ | #I = 1} = v →
        #{I ∈ Γ | q + 1 ≤ #I} ≤ v ^ q * 2 ^ d from
      this _ Δ hdown hcap rfl
    intro v
    induction v using Nat.strong_induction_on with
    | ind v ih_v =>
      intro Γ hΓ hΓcap hv
      set U₁ : Finset α := Γ.biUnion id
      have hU₁ : #U₁ = v := (card_biUnion_eq_card_singletons hΓ).trans hv
      have hsub {I : Finset α} (hI : I ∈ Γ) : I ⊆ U₁ :=
        mem_powerset.mp (subset_biUnion_powerset Γ hI)
      rcases Nat.eq_zero_or_pos v with rfl | hvpos
      · refine (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun I hI hIq => ?_)).trans_le
          (Nat.zero_le _)
        have := card_le_card (hsub hI)
        omega
      by_cases hvd : v ≤ d
      · have h2 : #Γ ≤ #U₁.powerset := card_le_card (subset_biUnion_powerset Γ)
        rw [card_powerset, hU₁] at h2
        exact (card_filter_le _ _).trans <| h2.trans <| (Nat.pow_le_pow_right two_pos hvd).trans
          (Nat.le_mul_of_pos_left _ (pow_pos hvpos q))
      push Not at hvd
      set Γtop : Finset (Finset α) := {E ∈ Γ | #E = q + 1}
      let deg (i : α) : ℕ := #{E ∈ Γtop | i ∈ E}
      obtain ⟨i₀, hi₀U, hmin⟩ := exists_min_image U₁ deg (card_pos.mp (hU₁.symm ▸ hvpos))
      have hsum_deg : ∑ i ∈ U₁, deg i = #Γtop * (q + 1) := by
        simp only [deg, card_filter]
        rw [sum_comm]
        refine sum_const_nat fun E hE => ?_
        rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr (hsub (mem_filter.mp hE).1),
          (mem_filter.mp hE).2]
      have hdeg_cap : q.factorial * deg i₀ ≤ d ^ q := by
        refine Nat.le_of_mul_le_mul_left ?_ hvpos
        have hmul : v * deg i₀ ≤ #Γtop * (q + 1) := by
          simpa only [hU₁, hsum_deg, nsmul_eq_mul, Nat.cast_id] using
            card_nsmul_le_sum U₁ deg (deg i₀) hmin
        calc v * (q.factorial * deg i₀) = q.factorial * (v * deg i₀) := by ring
          _ ≤ q.factorial * (#Γtop * (q + 1)) := Nat.mul_le_mul_left _ hmul
          _ = (q + 1).factorial * #Γtop := by rw [Nat.factorial_succ]; ring
          _ ≤ d ^ (q + 1) := hΓcap
          _ ≤ v * d ^ q := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hvd.le
      set Γdel : Finset (Finset α) := {I ∈ Γ | i₀ ∉ I}
      set Γlink : Finset (Finset α) := ({E ∈ Γ | i₀ ∈ E}).image (·.erase i₀)
      have hmem_link (J : Finset α) : J ∈ Γlink ↔ i₀ ∉ J ∧ insert i₀ J ∈ Γ := by
        simp only [Γlink, mem_image, mem_filter]
        constructor
        · rintro ⟨E, ⟨hEΓ, hiE⟩, rfl⟩
          exact ⟨notMem_erase i₀ E, (insert_erase hiE).symm ▸ hEΓ⟩
        · rintro ⟨hni, hins⟩
          exact ⟨insert i₀ J, ⟨hins, mem_insert_self i₀ J⟩, erase_insert hni⟩
      have hdel_down : ∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Γdel → J ∈ Γdel := by
        intro I J hJI hI
        obtain ⟨hIΓ, hni⟩ := mem_filter.mp hI
        exact mem_filter.mpr ⟨hΓ hJI hIΓ, fun hj => hni (hJI hj)⟩
      have hdel_cap : (q + 1).factorial * #{I ∈ Γdel | #I = q + 1} ≤ d ^ (q + 1) :=
        (Nat.mul_le_mul_left _ (card_le_card (filter_subset_filter _ (filter_subset _ _)))).trans
          hΓcap
      have hdel_1 : #{I ∈ Γdel | #I = 1} = v - 1 := by
        obtain ⟨E₀, hE₀, hi₀E⟩ := mem_biUnion.mp hi₀U
        have heq : ({I ∈ Γdel | #I = 1} : Finset _) =
            ({I ∈ Γ | #I = 1} : Finset _).erase {i₀} := by
          ext I
          simp only [Γdel, mem_filter, mem_erase]
          constructor
          · rintro ⟨⟨hI, hni⟩, hc⟩
            exact ⟨fun h => hni (h ▸ mem_singleton_self i₀), hI, hc⟩
          · rintro ⟨hne, hI, hc⟩
            obtain ⟨j, rfl⟩ := card_eq_one.mp hc
            exact ⟨⟨hI, fun hj => hne (by rw [mem_singleton.mp hj])⟩, card_singleton j⟩
        rw [heq, card_erase_of_mem (mem_filter.mpr ⟨hΓ (singleton_subset_iff.mpr hi₀E) hE₀,
          card_singleton i₀⟩), hv]
      have hlink_down : ∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Γlink → J ∈ Γlink := by
        intro I J hJI hI
        obtain ⟨hni, hins⟩ := (hmem_link I).mp hI
        exact (hmem_link J).mpr ⟨fun hj => hni (hJI hj), hΓ (insert_subset_insert i₀ hJI) hins⟩
      have hlink_1 : #{J ∈ Γlink | #J = 1} ≤ v - 1 := by
        rw [← hdel_1]
        refine card_le_card (filter_subset_filter _ fun J hJ => ?_)
        obtain ⟨hni, hins⟩ := (hmem_link J).mp hJ
        exact mem_filter.mpr ⟨hΓ (subset_insert i₀ J) hins, hni⟩
      have hlink_card (P : ℕ → Prop) [DecidablePred P] :
          #{J ∈ Γlink | P (#J + 1)} = #{I ∈ Γ | P #I ∧ i₀ ∈ I} := by
        refine card_nbij' (insert i₀) (·.erase i₀) (fun J hJ => ?_) (fun I hI => ?_)
          (fun J hJ => erase_insert ((hmem_link J).mp (mem_filter.mp hJ).1).1)
          fun I hI => insert_erase (mem_filter.mp hI).2.2
        · obtain ⟨hJl, hJP⟩ := mem_filter.mp hJ
          obtain ⟨hni, hins⟩ := (hmem_link J).mp hJl
          exact mem_filter.mpr ⟨hins, by rwa [card_insert_of_notMem hni], mem_insert_self i₀ J⟩
        · obtain ⟨hIΓ, hIP, hiI⟩ := mem_filter.mp hI
          refine mem_filter.mpr ⟨(hmem_link _).mpr ⟨notMem_erase i₀ I, ?_⟩, ?_⟩
          · rwa [insert_erase hiI]
          · rwa [card_erase_add_one hiI]
      have hlink_bound : #{J ∈ Γlink | q ≤ #J} ≤ (v - 1) ^ (q - 1) * 2 ^ d := by
        refine (ih_p hlink_down ?_).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlink_1 _))
        have h := hlink_card (· = q + 1)
        simp only [Nat.add_right_cancel_iff] at h
        simpa only [h, deg, Γtop, filter_filter] using hdeg_cap
      have hwith_card := hlink_card (q + 1 ≤ ·)
      simp only [Nat.add_le_add_iff_right] at hwith_card
      have hsplit : #{I ∈ Γ | q + 1 ≤ #I} =
          #{I ∈ Γdel | q + 1 ≤ #I} + #{I ∈ Γ | q + 1 ≤ #I ∧ i₀ ∈ I} := by
        rw [← card_filter_add_card_filter_not (s := ({I ∈ Γ | q + 1 ≤ #I} : Finset _))
          (fun I => i₀ ∉ I)]
        simp only [Γdel, filter_filter, not_not, and_comm]
      have hpow_step : (v - 1) ^ q + (v - 1) ^ (q - 1) ≤ v ^ q := by
        obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        calc u ^ (r + 1) + u ^ r = (u + 1) * u ^ r := by ring
          _ ≤ (u + 1) * (u + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) r)
          _ = (u + 1) ^ (r + 1) := (pow_succ' _ _).symm
      calc #{I ∈ Γ | q + 1 ≤ #I}
          = #{I ∈ Γdel | q + 1 ≤ #I} + #{J ∈ Γlink | q ≤ #J} := by rw [hsplit, hwith_card]
        _ ≤ (v - 1) ^ q * 2 ^ d + (v - 1) ^ (q - 1) * 2 ^ d :=
          add_le_add (ih_v (v - 1) (by omega) Γdel hdel_down hdel_cap hdel_1) hlink_bound
        _ ≤ v ^ q * 2 ^ d := by rw [← add_mul]; exact Nat.mul_le_mul_right _ hpow_step

end Finset
