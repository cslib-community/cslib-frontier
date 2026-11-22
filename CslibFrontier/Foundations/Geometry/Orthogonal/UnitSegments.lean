/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.Orthogonal.Neighborhood
public import CslibFrontier.Foundations.Geometry.Orthogonal.Separation

/-!
# Continuous contacts of lattice unit segments

Two different undirected lattice unit segments meet only at common endpoints. A route with
distinct listed points therefore has continuous simplicity. For different routes, excluding a
common undirected unit segment reduces every real contact to a shared listed grid point.

## Main results

* `Cslib.Orthogonal.endpointContacts_unit`: contacts between different undirected unit segments.
* `Cslib.Orthogonal.isSimple_of_unit_nodup`: distinct listed points suffice for unit routes.
* `Cslib.Orthogonal.contact_unit_routes`: a real contact of unit routes is a shared listed point.
-/

public section

namespace Cslib.Orthogonal

private theorem unit_cases {a b : Point} (h : length a b = 1) :
    b = (a.1 + 1, a.2) ∨ b = (a.1 - 1, a.2) ∨
      b = (a.1, a.2 + 1) ∨ b = (a.1, a.2 - 1) := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [length] at h
  simp only [Prod.mk.injEq]
  omega

private theorem unit_contact_check {a b c d : Point} (hab : length a b = 1)
    (hcd : length c d = 1) (hsame : (a, b) ≠ (c, d)) (hreverse : (a, b) ≠ (d, c)) :
    segmentContactCheck [a, b] a b c d = true := by
  rcases a with ⟨ax, ay⟩
  rcases c with ⟨cx, cy⟩
  obtain rfl | rfl | rfl | rfl := unit_cases hab
  all_goals obtain rfl | rfl | rfl | rfl := unit_cases hcd
  all_goals
    simp only [ne_eq, Prod.mk.injEq] at hsame hreverse
    simp only [segmentContactCheck, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq]
    omega

/-- Different undirected unit segments have only common-endpoint contacts in the real plane. -/
theorem endpointContacts_unit {a b c d : Point} (hab : length a b = 1)
    (hcd : length c d = 1) (hsame : (a, b) ≠ (c, d)) (hreverse : (a, b) ≠ (d, c)) :
    EndpointContacts a b c d := by
  intro p hp hq
  obtain ⟨x, hx, rfl⟩ := segmentContactCheck_sound
    (unit_contact_check hab hcd hsame hreverse) hp hq
  have hx' : x = a ∨ x = b := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx
  refine ⟨hx'.elim (fun h => .inl (congrArg realPoint h))
    (fun h => .inr (congrArg realPoint h)), ?_⟩
  exact (eq_endpoint_of_mem_unit_segment hcd hq).elim
    (fun h => .inl (congrArg realPoint h)) (fun h => .inr (congrArg realPoint h))

private theorem no_reverse_pairs {r : Route} (hn : r.Nodup) {e f : Point × Point}
    (he : e ∈ r.consecutivePairs) (hf : f ∈ r.consecutivePairs) (hne : e ≠ f) :
    e ≠ (f.2, f.1) := by
  induction r with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons a r ih =>
    cases r with
    | nil => exact False.elim (List.not_mem_nil he)
    | cons b r =>
      rcases List.mem_cons.1 he with rfl | he
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact False.elim (hne rfl)
        · intro h
          have ha : a ∈ b :: r := by
            have hm := List.of_mem_zip hf
            have heq : a = f.2 := congrArg Prod.fst h
            exact heq.symm ▸ List.mem_of_mem_tail hm.2
          exact (List.nodup_cons.1 hn).1 ha
      · rcases List.mem_cons.1 hf with rfl | hf
        · intro h
          have hm := List.of_mem_zip he
          have heq : e.2 = a := congrArg Prod.snd h
          exact (List.nodup_cons.1 hn).1 (heq ▸ List.mem_of_mem_tail hm.2)
        · exact ih hn.tail he hf

/-- A unit route with distinct listed points is continuously simple. -/
theorem isSimple_of_unit_nodup {r : Route} (hn : r.Nodup)
    (hu : ∀ e ∈ r.consecutivePairs, length e.1 e.2 = 1) : IsSimple r :=
  ⟨hn, fun e he f hf hne =>
    endpointContacts_unit (hu e he) (hu f hf) hne (no_reverse_pairs hn he hf hne)⟩

/-- A real contact between unit routes without a common undirected segment is a shared
listed lattice point. -/
theorem contact_unit_routes {r s : Route}
    (hr : ∀ e ∈ r.consecutivePairs, length e.1 e.2 = 1)
    (hs : ∀ e ∈ s.consecutivePairs, length e.1 e.2 = 1)
    (hseg : ∀ e ∈ r.consecutivePairs, ∀ f ∈ s.consecutivePairs,
      e ≠ f ∧ e ≠ (f.2, f.1)) {p : ℝ × ℝ}
    (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ x ∈ r, x ∈ s ∧ p = realPoint x := by
  rcases hp with ⟨x, hx, rfl⟩ | ⟨e, he, hp⟩
  · exact ⟨x, hx, (mem_iff_realPoint_mem_support hs x).2 hq, rfl⟩
  rcases hq with ⟨x, hx, rfl⟩ | ⟨f, hf, hq⟩
  · exact ⟨x, (mem_iff_realPoint_mem_support hr x).2 (.inr ⟨e, he, hp⟩), hx, rfl⟩
  obtain ⟨h₁, h₂⟩ := hseg e he f hf
  obtain ⟨hp', _⟩ := endpointContacts_unit (hr e he) (hs f hf) h₁ h₂ p hp hq
  rcases hp' with hp' | hp'
  · refine ⟨e.1, (List.of_mem_zip he).1, ?_, hp'⟩
    exact (mem_iff_realPoint_mem_support hs e.1).2 (hp' ▸ .inr ⟨f, hf, hq⟩)
  · refine ⟨e.2, List.mem_of_mem_tail (List.of_mem_zip he).2, ?_, hp'⟩
    exact (mem_iff_realPoint_mem_support hs e.2).2 (hp' ▸ .inr ⟨f, hf, hq⟩)

end Cslib.Orthogonal
