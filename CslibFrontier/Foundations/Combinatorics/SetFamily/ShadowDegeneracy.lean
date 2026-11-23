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
    have h1 : #{I ∈ Δ | 1 ≤ #I} ≤ #Δ := card_filter_le _ _
    have h2 : #Δ ≤ 2 ^ #(Δ.biUnion id) := by
      simpa only [card_powerset] using card_le_card (subset_biUnion_powerset Δ)
    rw [card_biUnion_eq_card_singletons hdown] at h2
    exact (h1.trans h2).trans (Nat.pow_le_pow_right (by decide : 0 < 2) hcap)
  | succ q hq ih_p =>
    simp only [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · rw [zero_pow (by omega)] at hcap
      have hemp0 : #{I ∈ Δ | #I = q + 1} = 0 :=
        (Nat.mul_eq_zero.mp (Nat.le_zero.mp hcap)).resolve_left (Nat.factorial_pos (q + 1)).ne'
      have hemp : ({I ∈ Δ | q + 1 ≤ #I} : Finset _) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro I hI
        obtain ⟨hIΔ, hIq⟩ := mem_filter.mp hI
        obtain ⟨J, hJI, hJcard⟩ := exists_subset_card_eq hIq
        have hJmem : J ∈ ({I ∈ Δ | #I = q + 1} : Finset _) :=
          mem_filter.mpr ⟨hdown hJI hIΔ, hJcard⟩
        have hpos : 0 < #{I ∈ Δ | #I = q + 1} := card_pos.mpr ⟨J, hJmem⟩
        omega
      rw [hemp, card_empty]
      exact Nat.zero_le _
    · suffices ∀ v (Γ : Finset (Finset α)),
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
        rcases Nat.eq_zero_or_pos v with rfl | hvpos
        · have hU₁_emp : U₁ = ∅ := card_eq_zero.mp hU₁
          have hemp : ({I ∈ Γ | q + 1 ≤ #I} : Finset _) = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro I hI
            obtain ⟨hIΓ, hIq⟩ := mem_filter.mp hI
            have hsubI : I ⊆ U₁ := mem_powerset.mp (subset_biUnion_powerset Γ hIΓ)
            rw [hU₁_emp, subset_empty] at hsubI
            subst hsubI
            simp at hIq
          rw [hemp, card_empty]
          exact Nat.zero_le _
        · by_cases hvd : v ≤ d
          · have h1 : #{I ∈ Γ | q + 1 ≤ #I} ≤ #Γ := card_filter_le _ _
            have h2 : #Γ ≤ 2 ^ v := by
              rw [← hU₁]
              simpa only [card_powerset] using card_le_card (subset_biUnion_powerset Γ)
            calc #{I ∈ Γ | q + 1 ≤ #I} ≤ 2 ^ v := h1.trans h2
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide : 0 < 2) hvd
              _ = 1 * 2 ^ d := (one_mul _).symm
              _ ≤ v ^ q * 2 ^ d := Nat.mul_le_mul_right _ (Nat.one_le_pow q v hvpos)
          · push Not at hvd
            set Γtop : Finset (Finset α) := {E ∈ Γ | #E = q + 1}
            let deg (i : α) : ℕ := #{E ∈ Γtop | i ∈ E}
            have hU₁_ne : U₁.Nonempty := card_pos.mp (hU₁.symm ▸ hvpos)
            obtain ⟨i₀, hi₀U, hmin⟩ := exists_min_image U₁ deg hU₁_ne
            have hsum_deg : ∑ i ∈ U₁, deg i = (q + 1) * #Γtop := by
              have hswap : (∑ i ∈ U₁, ∑ E ∈ Γtop, if i ∈ E then 1 else 0) =
                  ∑ E ∈ Γtop, ∑ i ∈ U₁, if i ∈ E then 1 else 0 := sum_comm
              have hinner_i (i : α) :
                  (∑ E ∈ Γtop, if i ∈ E then 1 else 0) = deg i := by
                simp only [deg, sum_boole, Nat.cast_id]
              have hinner_E (E : Finset α) (hE : E ∈ Γtop) :
                  (∑ i ∈ U₁, if i ∈ E then 1 else 0) = q + 1 := by
                obtain ⟨hEΓ, hEq⟩ := mem_filter.mp hE
                have hEU : E ⊆ U₁ := mem_powerset.mp (subset_biUnion_powerset Γ hEΓ)
                rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, inter_eq_right.mpr hEU, hEq]
              rw [← sum_congr rfl fun i _ => hinner_i i, hswap,
                sum_congr rfl hinner_E, sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]
            have hmul_deg : v * deg i₀ ≤ (q + 1) * #Γtop := by
              calc v * deg i₀ = ∑ _i ∈ U₁, deg i₀ := by
                    rw [sum_const, hU₁, nsmul_eq_mul, Nat.cast_id]
                _ ≤ ∑ i ∈ U₁, deg i := sum_le_sum fun i hi => hmin i hi
                _ = (q + 1) * #Γtop := hsum_deg
            have hdeg_cap : q.factorial * deg i₀ ≤ d ^ q := by
              have h1 : v * (q.factorial * deg i₀) ≤ d * d ^ q := by
                calc v * (q.factorial * deg i₀)
                    = q.factorial * (v * deg i₀) := by ring
                  _ ≤ q.factorial * ((q + 1) * #Γtop) := Nat.mul_le_mul_left _ hmul_deg
                  _ = (q + 1).factorial * #Γtop := by rw [Nat.factorial_succ]; ring
                  _ ≤ d ^ (q + 1) := hΓcap
                  _ = d * d ^ q := by rw [pow_succ']
              by_contra! hgt
              have h3 : d * d ^ q + 1 ≤ (d + 1) * (d ^ q + 1) := by ring_nf; omega
              have h4 : (d + 1) * (d ^ q + 1) ≤ v * (q.factorial * deg i₀) :=
                Nat.mul_le_mul hvd hgt
              omega
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
            have hdel_cap : (q + 1).factorial * #{I ∈ Γdel | #I = q + 1} ≤ d ^ (q + 1) := by
              refine (Nat.mul_le_mul_left _ (card_le_card fun I hI => ?_)).trans hΓcap
              obtain ⟨hIdel, hIq⟩ := mem_filter.mp hI
              exact mem_filter.mpr ⟨(mem_filter.mp hIdel).1, hIq⟩
            have hdel_1 : #{I ∈ Γdel | #I = 1} = v - 1 := by
              obtain ⟨E₀, hE₀, hi₀E⟩ := mem_biUnion.mp hi₀U
              have hi₀_mem : ({i₀} : Finset α) ∈ ({I ∈ Γ | #I = 1} : Finset _) :=
                mem_filter.mpr ⟨hΓ (singleton_subset_iff.mpr hi₀E) hE₀, card_singleton i₀⟩
              have heq : ({I ∈ Γdel | #I = 1} : Finset _) =
                  ({I ∈ Γ | #I = 1} : Finset _).erase {i₀} := by
                ext I
                simp only [Γdel, mem_filter, mem_erase]
                constructor
                · rintro ⟨⟨hI, hni⟩, hc⟩
                  exact ⟨fun h => hni (h ▸ mem_singleton_self i₀), hI, hc⟩
                · rintro ⟨hne, hI, hc⟩
                  obtain ⟨j, rfl⟩ := card_eq_one.mp hc
                  refine ⟨⟨hI, fun hj => hne ?_⟩, card_singleton j⟩
                  rw [mem_singleton.mp hj]
              rw [heq, card_erase_of_mem hi₀_mem, hv]
            have hdel_bound : #{I ∈ Γdel | q + 1 ≤ #I} ≤ (v - 1) ^ q * 2 ^ d :=
              ih_v (v - 1) (by omega) Γdel hdel_down hdel_cap hdel_1
            have hlink_down : ∀ ⦃I J : Finset α⦄, J ⊆ I → I ∈ Γlink → J ∈ Γlink := by
              intro I J hJI hI
              obtain ⟨hni, hins⟩ := (hmem_link I).mp hI
              exact (hmem_link J).mpr ⟨fun hj => hni (hJI hj),
                hΓ (insert_subset_insert i₀ hJI) hins⟩
            have hlink_1 : #{J ∈ Γlink | #J = 1} ≤ v - 1 := by
              rw [← hdel_1]
              refine card_le_card fun J hJ => ?_
              obtain ⟨hJl, hJq⟩ := mem_filter.mp hJ
              obtain ⟨hni, hins⟩ := (hmem_link J).mp hJl
              exact mem_filter.mpr ⟨mem_filter.mpr ⟨hΓ (subset_insert i₀ J) hins, hni⟩, hJq⟩
            have hlink_q : #{J ∈ Γlink | #J = q} = deg i₀ := by
              refine card_bij (fun J _ => insert i₀ J)
                (fun J hJ => by
                  obtain ⟨hJl, hJq⟩ := mem_filter.mp hJ
                  obtain ⟨hni, hins⟩ := (hmem_link J).mp hJl
                  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hins, by
                    rw [card_insert_of_notMem hni, hJq]⟩, mem_insert_self i₀ J⟩)
                (fun J₁ hJ₁ J₂ hJ₂ heq => by
                  have hni₁ := ((hmem_link J₁).mp (mem_filter.mp hJ₁).1).1
                  have hni₂ := ((hmem_link J₂).mp (mem_filter.mp hJ₂).1).1
                  have h := congrArg (fun S => S.erase i₀) heq
                  rwa [erase_insert hni₁, erase_insert hni₂] at h)
                fun E hE => by
                  obtain ⟨hEt, hiE⟩ := mem_filter.mp hE
                  obtain ⟨hEΓ, hEq⟩ := mem_filter.mp hEt
                  refine ⟨E.erase i₀, mem_filter.mpr ⟨(hmem_link _).mpr ⟨notMem_erase i₀ E, ?_⟩,
                    ?_⟩, insert_erase hiE⟩
                  · rw [insert_erase hiE]; exact hEΓ
                  · have := card_erase_of_mem hiE; omega
            have hlink_cap : q.factorial * #{J ∈ Γlink | #J = q} ≤ d ^ q := by
              rwa [hlink_q]
            have hlink_bound : #{J ∈ Γlink | q ≤ #J} ≤ (v - 1) ^ (q - 1) * 2 ^ d := by
              calc #{J ∈ Γlink | q ≤ #J}
                  ≤ #{J ∈ Γlink | #J = 1} ^ (q - 1) * 2 ^ d := ih_p hlink_down hlink_cap
                _ ≤ (v - 1) ^ (q - 1) * 2 ^ d :=
                    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlink_1 _)
            have hwith_card : #{I ∈ Γ | q + 1 ≤ #I ∧ i₀ ∈ I} = #{J ∈ Γlink | q ≤ #J} := by
              refine card_bij (fun I _ => I.erase i₀)
                (fun I hI => by
                  obtain ⟨hIΓ, hIq, hiI⟩ := mem_filter.mp hI
                  refine mem_filter.mpr ⟨(hmem_link _).mpr ⟨notMem_erase i₀ I, ?_⟩, ?_⟩
                  · rw [insert_erase hiI]; exact hIΓ
                  · have := card_erase_of_mem hiI; omega)
                (fun I₁ hI₁ I₂ hI₂ heq => by
                  have hi₁ := (mem_filter.mp hI₁).2.2
                  have hi₂ := (mem_filter.mp hI₂).2.2
                  rw [← insert_erase hi₁, ← insert_erase hi₂, heq])
                fun J hJ => by
                  obtain ⟨hJl, hJq⟩ := mem_filter.mp hJ
                  obtain ⟨hni, hins⟩ := (hmem_link J).mp hJl
                  refine ⟨insert i₀ J, mem_filter.mpr ⟨hins, ?_, mem_insert_self i₀ J⟩,
                    erase_insert hni⟩
                  rw [card_insert_of_notMem hni]
                  omega
            have hsplit : #{I ∈ Γ | q + 1 ≤ #I} =
                #{I ∈ Γdel | q + 1 ≤ #I} + #{I ∈ Γ | q + 1 ≤ #I ∧ i₀ ∈ I} := by
              set BIG := ({I ∈ Γ | q + 1 ≤ #I} : Finset _)
              have hp1 : ({I ∈ Γdel | q + 1 ≤ #I} : Finset _) =
                  BIG.filter (fun I => ¬ i₀ ∈ I) := by
                ext I; simp only [BIG, Γdel, mem_filter]; tauto
              have hp2 : ({I ∈ Γ | q + 1 ≤ #I ∧ i₀ ∈ I} : Finset _) =
                  BIG.filter (fun I => i₀ ∈ I) := by
                ext I; simp only [BIG, mem_filter]; tauto
              have hsum := card_filter_add_card_filter_not (s := BIG) (fun I => i₀ ∈ I)
              rw [hp1, hp2]
              omega
            have hpow_step : (v - 1) ^ q + (v - 1) ^ (q - 1) ≤ v ^ q := by
              set u := v - 1
              have huv : v = u + 1 := by omega
              have hqu : u ^ q = u * u ^ (q - 1) := by
                conv_lhs => rw [show q = q - 1 + 1 by omega, pow_succ']
              calc u ^ q + u ^ (q - 1) = (u + 1) * u ^ (q - 1) := by rw [hqu]; ring
                _ ≤ (u + 1) * (u + 1) ^ (q - 1) :=
                    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ u) _)
                _ = (u + 1) ^ q := by
                    conv_rhs => rw [show q = q - 1 + 1 by omega, pow_succ']
                _ = v ^ q := by rw [← huv]
            calc #{I ∈ Γ | q + 1 ≤ #I}
                = #{I ∈ Γdel | q + 1 ≤ #I} + #{J ∈ Γlink | q ≤ #J} := by
                  rw [hsplit, hwith_card]
              _ ≤ (v - 1) ^ q * 2 ^ d + (v - 1) ^ (q - 1) * 2 ^ d :=
                  Nat.add_le_add hdel_bound hlink_bound
              _ = ((v - 1) ^ q + (v - 1) ^ (q - 1)) * 2 ^ d := (add_mul _ _ _).symm
              _ ≤ v ^ q * 2 ^ d := Nat.mul_le_mul_right _ hpow_step

end Finset
