/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteGadget
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite rule tables over arbitrary finite alphabets

Enumerate a finite family of two-letter rules after renaming its alphabet with
`Fintype.equivFin`. The table retains exactly the original rules, and the symmetric standard
semi-Thue reachability relation is preserved in both directions for every pair of words.
This is infrastructure for instantiating the fixed-rule H-word compiler.

## Main definitions

* `HWord.RewriteGadget.RuleTable`: an indexed rule table with soundness and coverage.
* `HWord.RewriteGadget.RuleTable.ofFinite`: compile a finite single-letter two-letter rule family.

## Main results

* `HWord.RewriteGadget.RuleTable.reachable_iff`: exact source and table reachability equivalence.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

open Cslib.PostCorrespondence

variable {Γ : Type*} [Fintype Γ] (R : Domino Γ → Prop)

/-- A fixed finite table for a source rule family, with letters numbered by `Fintype.equivFin`. -/
structure RuleTable where
  /-- Number of entries in the fixed rule table. -/
  size : ℕ
  /-- The indexed single-letter two-letter rules. -/
  entries : Fin size → Rule (Fintype.card Γ)
  /-- Decoding an entry recovers a source rule. -/
  sound : ∀ i, R ⟨(entries i).domino.top.map (Fintype.equivFin Γ).symm,
    (entries i).domino.bottom.map (Fintype.equivFin Γ).symm⟩
  /-- Every source rule occurs in the table. -/
  complete : ∀ d, R d → ∃ i, (entries i).domino =
    ⟨d.top.map (Fintype.equivFin Γ), d.bottom.map (Fintype.equivFin Γ)⟩

private theorem exists_encoded_rule (d : Domino Γ)
    (hshape : ∃ a b c e, d.top = [a, b] ∧ d.bottom = [c, e] ∧ (a = c ∨ b = e)) :
    ∃ rule : Rule (Fintype.card Γ), rule.domino =
      ⟨d.top.map (Fintype.equivFin Γ), d.bottom.map (Fintype.equivFin Γ)⟩ := by
  obtain ⟨a, b, c, e, ht, hb, hchange⟩ := hshape
  refine ⟨⟨Fintype.equivFin Γ a, Fintype.equivFin Γ b, Fintype.equivFin Γ c,
    Fintype.equivFin Γ e, hchange.imp (congrArg _) (congrArg _)⟩, ?_⟩
  simp [Rule.domino, ht, hb]

/-- Enumerate a finite source family whose rules have length two and retain a context letter. -/
noncomputable def RuleTable.ofFinite (hfinite : {d | R d}.Finite)
    (hshape : ∀ d, R d →
      ∃ a b c e, d.top = [a, b] ∧ d.bottom = [c, e] ∧ (a = c ∨ b = e)) : RuleTable R := by
  letI : Fintype {d // R d} := hfinite.fintype
  let select (d : {d // R d}) :=
    Classical.choose (exists_encoded_rule d.val (hshape d.val d.property))
  have hselect (d : {d // R d}) : (select d).domino =
      ⟨d.val.top.map (Fintype.equivFin Γ), d.val.bottom.map (Fintype.equivFin Γ)⟩ :=
    Classical.choose_spec (exists_encoded_rule d.val (hshape d.val d.property))
  refine ⟨Fintype.card {d // R d}, fun i => select ((Fintype.equivFin _).symm i), ?_, ?_⟩
  · intro i
    rw [hselect]
    simpa using ((Fintype.equivFin {d // R d}).symm i).property
  · intro d hd
    refine ⟨Fintype.equivFin {d // R d} ⟨d, hd⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hselect ⟨d, hd⟩

variable {R} (T : RuleTable R)

private theorem encoded_mem (d : Domino Γ) (hd : R d ∨ R ⟨d.bottom, d.top⟩) :
    RuleSet T.entries ⟨d.top.map (Fintype.equivFin Γ), d.bottom.map (Fintype.equivFin Γ)⟩ := by
  rcases hd with hd | hd
  · obtain ⟨i, hi⟩ := T.complete d hd
    exact ⟨i, Or.inl hi.symm⟩
  · obtain ⟨i, hi⟩ := T.complete ⟨d.bottom, d.top⟩ hd
    exact ⟨i, Or.inr (congrArg (fun e : Domino (Fin (Fintype.card Γ)) =>
      (⟨e.bottom, e.top⟩ : Domino (Fin (Fintype.card Γ)))) hi).symm⟩

private theorem decoded_mem (d : Domino (Fin (Fintype.card Γ)))
    (hd : RuleSet T.entries d) :
    R ⟨d.top.map (Fintype.equivFin Γ).symm, d.bottom.map (Fintype.equivFin Γ).symm⟩ ∨
      R ⟨d.bottom.map (Fintype.equivFin Γ).symm, d.top.map (Fintype.equivFin Γ).symm⟩ := by
  obtain ⟨i, rfl | rfl⟩ := hd
  · exact Or.inl (T.sound i)
  · exact Or.inr (T.sound i)

private theorem encode_step {s t : List Γ}
    (h : Rewrites (fun d => R d ∨ R ⟨d.bottom, d.top⟩) s t) :
    Rewrites (RuleSet T.entries) (s.map (Fintype.equivFin Γ)) (t.map (Fintype.equivFin Γ)) := by
  obtain ⟨before, d, after, hd, rfl, rfl⟩ := h
  exact ⟨before.map (Fintype.equivFin Γ),
    ⟨d.top.map (Fintype.equivFin Γ), d.bottom.map (Fintype.equivFin Γ)⟩,
    after.map (Fintype.equivFin Γ), encoded_mem T d hd,
    by simp only [List.map_append], by simp only [List.map_append]⟩

private theorem decode_step {s t : List (Fin (Fintype.card Γ))}
    (h : Rewrites (RuleSet T.entries) s t) :
    Rewrites (fun d => R d ∨ R ⟨d.bottom, d.top⟩)
      (s.map (Fintype.equivFin Γ).symm) (t.map (Fintype.equivFin Γ).symm) := by
  obtain ⟨before, d, after, hd, rfl, rfl⟩ := h
  exact ⟨before.map (Fintype.equivFin Γ).symm,
    ⟨d.top.map (Fintype.equivFin Γ).symm, d.bottom.map (Fintype.equivFin Γ).symm⟩,
    after.map (Fintype.equivFin Γ).symm, decoded_mem T d hd,
    by simp only [List.map_append], by simp only [List.map_append]⟩

/-- Symmetric standard semi-Thue reachability is unchanged by the finite table compilation. -/
theorem RuleTable.reachable_iff (s t : List Γ) :
    Relation.ReflTransGen (Rewrites (fun d => R d ∨ R ⟨d.bottom, d.top⟩)) s t ↔
      Relation.ReflTransGen (Rewrites (RuleSet T.entries))
        (s.map (Fintype.equivFin Γ)) (t.map (Fintype.equivFin Γ)) := by
  constructor
  · exact fun h => h.lift (List.map (Fintype.equivFin Γ)) (fun _ _ => encode_step T)
  · intro h
    have hd := h.lift (List.map (Fintype.equivFin Γ).symm) (fun _ _ => decode_step T)
    change Relation.ReflTransGen (Rewrites (fun d => R d ∨ R ⟨d.bottom, d.top⟩))
      ((s.map (Fintype.equivFin Γ)).map (Fintype.equivFin Γ).symm)
      ((t.map (Fintype.equivFin Γ)).map (Fintype.equivFin Γ).symm) at hd
    simpa using hd

end Cslib.Complexity.NCL.HWord.RewriteGadget
