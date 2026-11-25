/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence
import Mathlib.Data.List.Basic

/-!
# Counted criterion for edge instances

A duplicate-free scope and exactly two global occurrences per occurring variable imply the
existing positional `EdgeInstance` condition. Constraint records may repeat: constraint indices,
rather than record equality, distinguish their two endpoints.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

omit [DecidableEq V] in
/-- A duplicate-free scope identifies an occurrence from its constraint and variable. -/
theorem Occurrence.eq_of_scope_nodup (hscope : ∀ c ∈ F, c.scope.Nodup)
    {o p : F.Occurrence} (hi : o.1 = p.1) (hv : o.var = p.var) : o = p := by
  rcases o with ⟨i, j⟩
  rcases p with ⟨k, l⟩
  obtain rfl : i = k := hi
  congr
  exact Fin.ext ((hscope F[i.val] (List.getElem_mem i.isLt)).getElem_inj_iff.mp hv)

/-- Two total occurrences, with no repetition inside a scope, are exactly an edge's endpoints.
Only the actual variable list is counted; no finite universe or maximum name is required. -/
theorem edgeInstance_of_count_eq_two (hscope : ∀ c ∈ F, c.scope.Nodup)
    (hcount : ∀ v ∈ F.vars, F.vars.count v = 2) : EdgeInstance F := by
  intro o
  let records := F.occurrences.filter fun r => r.2.2 == o.var
  have hlen : records.length = 2 := by
    have hc := hcount o.var o.var_mem
    rw [← map_occurrences F, List.count_eq_countP, List.countP_map] at hc
    simpa only [records, ← List.countP_eq_length_filter, Function.comp_def] using hc
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha : a ∈ records := by simp [hab]
  have hb : b ∈ records := by simp [hab]
  have hne : a ≠ b := by
    have hn : records.Nodup := F.occurrences_nodup.filter _
    simpa [hab] using hn
  obtain ⟨oa, hoa⟩ := mem_occurrences.mp (List.mem_filter.mp ha).1
  obtain ⟨ob, hob⟩ := mem_occurrences.mp (List.mem_filter.mp hb).1
  have hva : oa.var = o.var := by
    simpa [← hoa, Occurrence.record] using (List.mem_filter.mp ha).2
  have hvb : ob.var = o.var := by
    simpa [← hob, Occurrence.record] using (List.mem_filter.mp hb).2
  have honly (q : F.Occurrence) (hv : q.var = o.var) : q = oa ∨ q = ob := by
    have hq : q.record ∈ records :=
      List.mem_filter.mpr ⟨mem_occurrences.mpr ⟨q, rfl⟩, by simp [Occurrence.record, hv]⟩
    rcases (by simpa [hab] using hq : q.record = a ∨ q.record = b) with hq | hq
    · exact .inl (Occurrence.record_injective (hq.trans hoa.symm))
    · exact .inr (Occurrence.record_injective (hq.trans hob.symm))
  have hdiff : oa.1 ≠ ob.1 := fun hi => hne <|
    hoa.symm.trans ((congrArg Occurrence.record
      (Occurrence.eq_of_scope_nodup hscope hi (hva.trans hvb.symm))).trans hob)
  rcases honly o rfl with rfl | rfl
  · exact ⟨ob, hdiff, hvb.symm, honly⟩
  · exact ⟨oa, hdiff.symm, hva.symm, fun q hv => (honly q hv).symm⟩

end Cslib.Logic.PL.CSP
