/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Edge.Defects

/-!
# Congruence of variable and set defects under port agreement

Agreement of two occurrence labelings on all ports of a variable preserves its defect
status (`inconsistent_congr`), and agreement on all ports whose variables belong to a
finite set preserves the defects in that set (`defects_inter_eq_of_eqOn`).
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

/-- Agreement at all actual ports of one variable preserves its exact defect status. -/
theorem inconsistent_congr {f g : OccurrenceLabeling F Bool} {v : V}
    (h : ∀ o : Occurrence F, o.var = v → f o = g o) :
    Inconsistent f v ↔ Inconsistent g v := by
  constructor
  · rintro ⟨o, p, ho, hp, hn⟩
    exact ⟨o, p, ho, hp, by rwa [← h o ho, ← h p hp]⟩
  · rintro ⟨o, p, ho, hp, hn⟩
    exact ⟨o, p, ho, hp, by rwa [h o ho, h p hp]⟩

/-- Agreement on a finite variable set preserves exactly the defects in that set. -/
theorem defects_inter_eq_of_eqOn [DecidableEq V] {f g : OccurrenceLabeling F Bool}
    (vs : Finset V) (h : ∀ o : Occurrence F, o.var ∈ vs → f o = g o) :
    defects f ∩ vs = defects g ∩ vs := by
  ext v
  simp only [Finset.mem_inter, mem_defects]
  by_cases hv : v ∈ vs
  · exact and_congr_left (fun _ => inconsistent_congr (fun o ho => h o (ho ▸ hv)))
  · simp only [hv, and_false]

end Cslib.Logic.PL.CSP
