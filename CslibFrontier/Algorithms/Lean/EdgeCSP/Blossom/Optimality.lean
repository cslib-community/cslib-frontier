/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Projection
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Lifting

/-!
# Forward improvement and reference optimality transfer

Lemma 42 of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 20, transfers
optimality of the contracted reference back to the prepared original labeling. The constructive
forward map below projects an original augmentation, stopping at its first internal port when
necessary. Together with `liftComparison_spec`, it supplies the two mathematical outcomes
needed after recursively optimizing the actual contracted instance.
-/

public section

namespace Cslib.Logic.PL.CSP.Blossom

open Table Finset
open Cslib.BitString
open scoped symmDiff

variable {F : CSP Table ℕ} {w p : Walk F}

/-- Project an original augmenting walk, stopping at its first blossom variable if it enters.
The all-outside case retains the honest reference central row. The entering case changes the
central row to the actual touched-constraint indicator of the first internal port. -/
@[expose] def projectAugmentation (f : OccurrenceLabeling F Bool) (w p : Walk F) :
    Option (OccurrenceLabeling (contract f (internal w)) Bool) :=
  let vs := internal w
  if p.edges.all (fun o => !vs.contains o.var) then some (projectZero f vs (p.flip f)) else
    let k := p.boundaryIndex vs
    if hk : k < p.steps.length then
      let (_, output) := p.steps[k]
      some (projectOne f vs ((p.take (k + 1)).flip f) output.1)
    else none

/-- The executable forward construction projects every actual original augmentation starting
away from the base and removes exactly two contracted-reference defects. -/
theorem projectAugmentation_spec (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f) (hp : p.IsAugmenting sem f)
    (hx : p.start ≠ w.start) :
    ∃ g, projectAugmentation f w p = some g ∧ ValidLabeling sem g ∧
      (defects g).card + 2 = (defects f).card := by
  let vs := internal w
  have hne := touched_ne_nil w hb.2.2.1
  have hroot : p.start ∈ defects f := mem_defects.mpr hp.2.1
  have hstart : p.start ∉ vs := fun hv => hx <| mem_singleton.mp <|
    defects_inter_internal hb ▸ mem_inter.mpr ⟨hroot, List.mem_toFinset.mpr hv⟩
  by_cases hall : p.edges.all (fun o => !vs.contains o.var) = true
  · have hagree : ∀ o : Occurrence F, o.var ∈ vs → p.flip f o = f o := fun o ho => by
      have hn : o ∉ p.edges := fun hm => by simpa [ho] using List.all_eq_true.mp hall o hm
      simp [Walk.flip, BitString.flipOn_apply, hn]
    have hv : ValidLabeling sem (p.flip f) := by
      simpa only [Walk.take, List.take_length] using hp.1.1.valid_take p.steps.length le_rfl
    have hcard := card_defects_transport_zero hF f (p.flip f) vs hne
    have hi := defects_inter_eq_of_eqOn vs.toFinset
      (fun o ho => hagree o (List.mem_toFinset.mp ho))
    rw [hi, defects_inter_internal hb, card_singleton] at hcard
    have ha := hp.card_defects_flip_add_two hF
    refine ⟨projectZero f vs (p.flip f), by unfold projectAugmentation; exact ite_eq_left hall,
      valid_projectZero hf hv vs hne hagree, ?_⟩
    dsimp only [projectZero]; omega
  · have hex : ∃ o ∈ p.edges, o.var ∈ vs := by
      simpa only [List.all_eq_true, Bool.not_eq_true', not_forall, Bool.not_eq_false,
        List.contains_iff_mem, exists_prop] using hall
    obtain ⟨hk, hevs, hbefore⟩ := Walk.boundaryIndex_spec hp.1.1.1 vs hstart hex
    let k := p.boundaryIndex vs
    let a := p.steps[k].1
    let e := p.steps[k].2
    let current := (p.take (k + 1)).flip f
    have haout : a.var ∉ vs := (hp.1.1.1.input_eq_finish_take k hk).symm ▸
      (p.take k).finish_property (P := fun v => v ∉ vs) hstart hbefore
    have hinside : ∀ o : Occurrence F, o.var ∈ vs →
        current o = if o = e then !(f o) else f o := by
      intro o ho
      have hn : o ∉ (p.take k).edges := fun hm => hbefore o hm ho
      have hna : o ≠ a := fun he => haout (congrArg Occurrence.var he ▸ ho)
      have hedges : (p.take (k + 1)).edges = (p.take k).edges ++ [a, e] := by
        rw [Walk.edges, Walk.take, List.take_succ_eq_append_getElem hk, Walk.edgesOf_append]
        rfl
      simp only [current, Walk.flip, BitString.flipOn_apply, List.mem_toFinset, hedges,
        List.mem_append, List.mem_cons, List.not_mem_nil, hn, hna, false_or, or_false]
    have hvalid : ValidLabeling sem current := hp.1.1.valid_take (k + 1) (by omega)
    have hd : defects current \ vs.toFinset = (defects f \ vs.toFinset).erase p.start := by
      rw [(hp.1.1.1.take (k + 1)).defects_flip hF, Walk.finish_take_succ p hk]
      change (defects f ∆ {p.start} ∆ {e.var}) \ vs.toFinset =
        (defects f \ vs.toFinset).erase p.start
      ext v
      simp only [mem_sdiff, Finset.mem_symmDiff, mem_singleton, mem_erase, List.mem_toFinset]
      by_cases hv : v ∈ vs
      · simp only [hv, not_true_eq_false, and_false]
      · have hve : v ≠ e.var := fun he => hv (he.symm ▸ hevs)
        by_cases hvr : v = p.start
        · subst v; simp [hroot, hve, hstart]
        · simp [hv, hve, hvr]
    have hcount := card_erase_add_one
      (mem_sdiff.mpr ⟨hroot, List.mem_toFinset.not.mpr hstart⟩)
    have htotal := card_sdiff_add_card_inter (defects f) vs.toFinset
    rw [defects_inter_internal hb, card_singleton] at htotal
    refine ⟨projectOne f vs current e.1,
      by unfold projectAugmentation; rw [ite_eq_right hall]; exact dite_eq_left hk,
      valid_projectOne hf hvalid vs e hevs hinside, ?_⟩
    rw [defects_projectOne hF, hd]
    omega

/-- Lemma 42 for the actual executable whole-instance contraction. Optimality of its prepared
reference implies optimality of the original prepared labeling, with no model or oracle. -/
theorem isOptimal_of_reference (hF : EdgeInstance F) {f : OccurrenceLabeling F Bool}
    (hb : w.IsBlossom sem f) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F)
    (hopt : IsOptimalLabeling sem (reference f (internal w))) : IsOptimalLabeling sem f := by
  refine ⟨hf, fun g hg => not_lt.mp fun hlt => ?_⟩
  obtain ⟨p, _, hp, hx, _⟩ := hF.augmentingWalk_spec hM hf hg hlt w.start
  obtain ⟨comparison, _, hv, hc⟩ := projectAugmentation_spec hF hb hf hp hx
  have ho := hopt.2 comparison hv
  rw [card_defects_reference_blossom hF hb] at ho
  omega

end Cslib.Logic.PL.CSP.Blossom
