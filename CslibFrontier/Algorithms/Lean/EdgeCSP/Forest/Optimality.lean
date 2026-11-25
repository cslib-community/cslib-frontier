/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Invariant
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Frontier
import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.ExchangeBound
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Optimality of a fresh exhausted forest search

`search_exhausted_isOptimalLabeling` proves the conclusion of Lemma 45 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 0:22–23: when the fresh
forest search exhausts its frontier before augmentation or a blossom, its valid base labeling
has the fewest defects among all valid labelings. Constraints are nonempty even delta-matroids
on their actual argument positions; their common parities may be odd. Variables need only
decidable equality, since all counts range over occurring variables and positional ports.

This is an alternative counting reconstruction, rather than the paper's shortest-bad-walk
proof. Saturation gives a local disagreement bound by one-sided exchange. Fresh roots and
unique children give the opposite global bound on changes at incoming and outgoing ports.
No terminal-event correctness, blossom contraction, native runtime or full solver is claimed.

## Main results

* `search_exhausted_isOptimalLabeling`: actual fresh exhaustion implies optimality.
-/

public section

namespace Cslib.Logic.PL.CSP.Forest

open Finset BitString DAG

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

private theorem outgoing_injective {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F}
    (hg : Grown sem f rs es) {a b : Occurrence F}
    (ha : a ∈ es.outgoing) (hb : b ∈ es.outgoing) (he : a.var = b.var) : a = b :=
  List.inj_on_of_nodup_map (by rw [← Log.children_eq_map_outgoing]; exact hg.children_nodup)
    ha hb he

private theorem incoming_saturated {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {rs : List V} {es : Log F}
    (hg : Grown sem f rs es) {a b : Occurrence F}
    (ha : a ∈ es.used.toFinset \ es.outgoing.toFinset)
    (hb : b ∈ partners sem f a) : b ∈ es.outgoing.toFinset := by
  obtain ⟨hau, hao⟩ := mem_sdiff.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (by rwa [Log.map_arcs_occurrence, ← List.mem_toFinset])
  obtain ⟨d, hd, he, hi, _⟩ := hg.saturated hc (Bool.eq_true_of_not_eq_false fun hi =>
    hao (List.mem_toFinset.mpr (Log.mem_outgoing_of_arc hc hi))) hb
  exact List.mem_toFinset.mpr (he ▸ Log.mem_outgoing_of_arc hd hi)

/-- Count changes by constraint positions, applying the local exchange bound on each actual
scope. The incoming and outgoing sets here are finite positional port sets. -/
private theorem local_changes_le {sem : Rel → List Bool → Bool}
    {f g : OccurrenceLabeling F Bool} (hF : EdgeInstance F)
    (hM : EdgeInstance.EvenConstraints sem F)
    (hf : ValidLabeling sem f) (hg : ValidLabeling sem g)
    (I O : Finset (Occurrence F)) (hIO : Disjoint I O)
    (hs : ∀ a ∈ I, ∀ b ∈ partners sem f a, b ∈ O) :
    (I.filter fun o => f o ≠ g o).card ≤ (O.filter fun o => f o ≠ g o).card := by
  have hlocal (i : Fin F.length) :
      ((univ.filter fun j => (⟨i, j⟩ : Occurrence F) ∈ I).filter
        fun j => f ⟨i, j⟩ ≠ g ⟨i, j⟩).card ≤
      ((univ.filter fun j => (⟨i, j⟩ : Occurrence F) ∈ O).filter
        fun j => f ⟨i, j⟩ ≠ g ⟨i, j⟩).card := by
    apply (hM i).card_disagree_le (hf i) (hg i)
    · exact disjoint_left.mpr fun j hjI hjO =>
        disjoint_left.mp hIO (mem_filter.mp hjI).2 (mem_filter.mp hjO).2
    · exact fun a ha b hb hba hv => hb <| mem_filter.mpr ⟨mem_univ b,
        hs _ (mem_filter.mp ha).2 _ <| (mem_partners sem f _ _).mpr
          ⟨rfl, hF.var_ne_of_constraint_eq rfl (sigma_mk_injective.ne hba.symm),
            pairFlip_eq f (sigma_mk_injective.ne hba.symm) ▸
              EdgeInstance.validLabeling_flipOn_pair hf i a b hv⟩⟩
  have hcount (P : Finset (Occurrence F)) :
      (∑ i : Fin F.length, ((univ.filter fun j => (⟨i, j⟩ : Occurrence F) ∈ P).filter
        fun j => f ⟨i, j⟩ ≠ g ⟨i, j⟩).card) = (P.filter fun o => f o ≠ g o).card := by
    simp only [filter_filter, card_filter]
    rw [← Fintype.sum_sigma (fun o : Occurrence F => if o ∈ P ∧ f o ≠ g o then 1 else 0),
      ← card_filter, ← card_filter]
    exact congrArg card (ext fun o => by simp only [mem_filter, mem_univ, true_and])
  simpa only [hcount] using sum_le_sum fun i (_ : i ∈ univ) => hlocal i

private theorem fiber_card (hF : EdgeInstance F) (s : Finset (Occurrence F))
    (o : Occurrence F) :
    (s.filter fun a => a.var = o.var).card =
      (if o ∈ s then 1 else 0) + (if hF.partner o ∈ s then 1 else 0) := by
  have he : (s.filter fun a => a.var = o.var) =
      ({o, hF.partner o} : Finset (Occurrence F)).filter (· ∈ s) := by
    ext a
    simp only [mem_filter, mem_insert, mem_singleton]
    exact ⟨fun ⟨ha, hv⟩ => ⟨hF.eq_or_eq_partner hv, ha⟩,
      by rintro ⟨rfl | rfl, ha⟩; exacts [⟨ha, rfl⟩, ⟨ha, (hF.partner_variable o).symm⟩]⟩
  rw [he]
  by_cases ho : o ∈ s <;> by_cases hp : hF.partner o ∈ s <;>
    simp [filter_insert, filter_singleton, ho, hp, hF.partner_ne o]

/-- The two endpoints of one edge account for a lost defect or an outgoing change by an
incoming change. Roots have two inputs; outputs have an input at their initially equal end. -/
private theorem variable_accounting (hF : EdgeInstance F)
    (f g : OccurrenceLabeling F Bool) (I O : Finset (Occurrence F))
    (hIO : Disjoint I O)
    (hr : ∀ o, Inconsistent f o.var → o ∈ I)
    (ho : ∀ o ∈ O, hF.partner o ∈ I ∧ ¬ Inconsistent f o.var)
    (o : Occurrence F) :
    (if Inconsistent f o.var then 1 else 0) +
        ((O.filter fun a => f a ≠ g a).filter fun a => a.var = o.var).card ≤
      (if Inconsistent g o.var then 1 else 0) +
        ((I.filter fun a => f a ≠ g a).filter fun a => a.var = o.var).card := by
  rw [fiber_card hF, fiber_card hF]
  have hIO' := disjoint_left.mp hIO
  by_cases hinc : Inconsistent f o.var
  · have hi := hr o hinc
    have hip := hr (hF.partner o) (by rwa [← hF.partner_variable o])
    simp only [hinc, ↓reduceIte, mem_filter, hIO' hi, hIO' hip, hi, hip, false_and, true_and]
    simp only [hF.inconsistent_iff] at hinc ⊢
    split_ifs <;> first | omega | simp_all
  · by_cases hout : o ∈ O
    · have hip := (ho o hout).1
      have hni : o ∉ I := fun h => hIO' h hout
      simp only [hinc, ↓reduceIte, mem_filter, hout, hip, hni, hIO' hip, false_and, true_and]
      simp only [hF.inconsistent_iff] at hinc ⊢
      split_ifs <;> first | omega | simp_all
    · by_cases houtp : hF.partner o ∈ O
      · have hi := hF.partner_partner o ▸ (ho (hF.partner o) houtp).1
        have hnip : hF.partner o ∉ I := fun h => hIO' h houtp
        simp only [hinc, ↓reduceIte, mem_filter, hout, houtp, hi, hnip, false_and, true_and]
        simp only [hF.inconsistent_iff] at hinc ⊢
        split_ifs <;> first | omega | simp_all
      · simp [hinc, hout, houtp]

private theorem global_changes_le (hF : EdgeInstance F)
    (f g : OccurrenceLabeling F Bool) (I O : Finset (Occurrence F))
    (hIO : Disjoint I O)
    (hr : ∀ o, Inconsistent f o.var → o ∈ I)
    (ho : ∀ o ∈ O, hF.partner o ∈ I ∧ ¬ Inconsistent f o.var) :
    (defects f).card + (O.filter fun o => f o ≠ g o).card ≤
      (defects g).card + (I.filter fun o => f o ≠ g o).card := by
  let vs := F.vars.toFinset
  have hpoint (v : V) (hv : v ∈ vs) :
      (if Inconsistent f v then 1 else 0) +
          ((O.filter fun a => f a ≠ g a).filter fun a => a.var = v).card ≤
        (if Inconsistent g v then 1 else 0) +
          ((I.filter fun a => f a ≠ g a).filter fun a => a.var = v).card := by
    obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hv)
    exact variable_accounting hF f g I O hIO hr ho o
  have hfiber (s : Finset (Occurrence F)) :
      (∑ v ∈ vs, (s.filter fun a => a.var = v).card) = s.card :=
    (card_eq_sum_card_fiberwise fun a _ => List.mem_toFinset.mpr a.var_mem).symm
  have hd (l : OccurrenceLabeling F Bool) :
      (∑ v ∈ vs, if Inconsistent l v then 1 else 0) = (defects l).card := by
    rw [sum_boole]
    exact congrArg card <| ext fun v => by
      simp only [mem_filter, mem_defects, vs, List.mem_toFinset]
      exact and_iff_right_of_imp fun ⟨o, _, hv, _, _⟩ => (exists_occurrence_iff v).mp ⟨o, hv⟩
  simpa only [sum_add_distrib, hfiber, hd] using sum_le_sum hpoint

/-- Lemma 45 of [KazdaKolmogorovRolinek2018], printed pp. 0:22–23, by an alternative
counting proof. A fresh executable search returning exhaustion certifies that its valid base
labeling minimizes defects among all valid labelings. No finite universe of variable names,
comparison labeling, supplied forest invariant or terminal-event theorem is required. -/
theorem search_exhausted_isOptimalLabeling (sem : Rel → List Bool → Bool)
    (f : OccurrenceLabeling F Bool) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F)
    {es : Log F} (hs : search sem f = .exhausted es) : IsOptimalLabeling sem f := by
  have hg := search_grown sem f hF; rw [hs] at hg
  have hc := search_exhausted_frontier sem f hs
  let O := es.outgoing.toFinset; let I := es.used.toFinset \ O
  have hIO : Disjoint I O := disjoint_sdiff_self_left
  have hroot (o : Occurrence F) (hi : Inconsistent f o.var) : o ∈ I :=
    mem_sdiff.mpr ⟨List.mem_toFinset.mpr (hc o (Or.inl ((mem_roots f _).mpr hi))),
      fun ho => hg.outgoing_not_root (List.mem_toFinset.mp ho) ((mem_roots f _).mpr hi)⟩
  have hout (o : Occurrence F) (ho : o ∈ O) : hF.partner o ∈ I ∧ ¬ Inconsistent f o.var := by
    have hom := List.mem_toFinset.mp ho
    refine ⟨mem_sdiff.mpr ⟨List.mem_toFinset.mpr (hc _ (hF.partner_variable o ▸
        Log.Grown.used_visited hg (es.outgoing_subset_used hom))),
      fun hp => hF.partner_ne o (outgoing_injective hg hom (List.mem_toFinset.mp hp)
        (hF.partner_variable o))⟩,
      fun hi => hg.outgoing_not_root hom ((mem_roots f _).mpr hi)⟩
  refine ⟨hf, fun g hvalid => ?_⟩
  have := local_changes_le hF hM hf hvalid I O hIO fun _ ha _ hb => incoming_saturated hg ha hb
  have := global_changes_le hF f g I O hIO hroot hout
  omega

end Cslib.Logic.PL.CSP.Forest
