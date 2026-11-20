/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.EmptinessSound
import CslibFrontier.Foundations.Data.List.Extract
import Mathlib.Data.List.Forall2

/-! # Completeness of the emptiness procedure

If an MPDA has a `K`-hole-bounded accepting run, the repaired search of Algorithm 1 of
[AkshayGastinKrishnaRoychowdhury2020] (`MPDA.isEmpty`) answers `false`.

The run is cut at its events: the positions after a maximal well-nested factor, where the next
transition is a pop or a push that is not closed by a well-nested continuation (`MPDA.wnEnd`). A
hole push opens a chain, which extends greedily by the least later hole push of the same stack
behind a well-nested factor; the chain is one `AddHole` step. A pop matches the newest push of the
last chain of its stack and is one `AddPop` step. When a chain opens, Definition 1 counts at least
one more open hole than there are open chains, so a `K`-hole-bounded run never needs more than `K`
of them.

## Main results

- `MPDA.isEmpty_eq_false_of_mem_boundedLanguage`: if some word has a `K`-hole-bounded accepting
  run, the search answers `false`.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α : Type*}

/-! ## The next event -/

section Events

variable (w : List (α × Op n Γ))

open Classical in
/-- The end of the longest well-nested factor of `w` starting at `p`. -/
noncomputable def wnEnd (p : ℕ) : ℕ :=
  Nat.findGreatest (fun r => p ≤ r ∧ WellNested (w.extract p r)) w.length

variable {w} {p r : ℕ}

theorem wnEnd_spec (hp : p ≤ w.length) :
    p ≤ wnEnd w p ∧ wnEnd w p ≤ w.length ∧ WellNested (w.extract p (wnEnd w p)) := by
  classical
  have hP : p ≤ p ∧ WellNested (w.extract p p) := ⟨le_rfl, by
    rw [List.extract_eq_take_drop, Nat.sub_self, List.take_zero]
    exact .nil⟩
  have := Nat.findGreatest_spec (P := fun r => p ≤ r ∧ WellNested (w.extract p r)) hp hP
  exact ⟨this.1, Nat.findGreatest_le _, this.2⟩

theorem le_wnEnd (hr : r ≤ w.length) (hpr : p ≤ r) (hwn : WellNested (w.extract p r)) :
    r ≤ wnEnd w p := by
  classical
  exact Nat.le_findGreatest (P := fun r => p ≤ r ∧ WellNested (w.extract p r)) hr ⟨hpr, hwn⟩

/-- After the longest well-nested factor comes an event: not a `nop`, and not a push closed by a
well-nested continuation. -/
theorem wnEnd_event (hp : p ≤ w.length) (hlt : wnEnd w p < w.length) :
    (¬∃ a, w[wnEnd w p]? = some (a, .nop)) ∧ ¬WellMatched w (wnEnd w p) := by
  obtain ⟨hpe, -, hwn⟩ := wnEnd_spec hp
  constructor
  · rintro ⟨a, ha⟩
    have hext : WellNested (w.extract p (wnEnd w p + 1)) := by
      rw [← w.extract_append_extract hpe (Nat.le_succ _), List.extract_eq_singleton ha]
      exact hwn.append (.nop .nil)
    have := le_wnEnd (show wnEnd w p + 1 ≤ w.length by omega) (by omega) hext
    omega
  · rintro ⟨m, hm, hmwn⟩
    have hmlen := hm.lt_length
    have hext : WellNested (w.extract p (m + 1)) := by
      rw [← w.extract_append_extract hpe (show wnEnd w p ≤ m + 1 by have := hm.1; omega)]
      exact hwn.append hmwn
    have := le_wnEnd (show m + 1 ≤ w.length by omega) (by have := hm.1; omega) hext
    have := hm.1
    omega

end Events

/-! ## Greedy chains -/

section Chains

open Classical

variable {w : List (α × Op n Γ)}

/-- A push on stack `i` that is not closed by a well-nested continuation. -/
@[expose] def IsHolePushOn (w : List (α × Op n Γ)) (i : Fin n) (r : ℕ) : Prop :=
  IsPushOn w i r ∧ ¬WellMatched w r

/-- The hole push at `r` extends a chain ending in the push at `q`: same stack, separated by a
well-nested factor. -/
@[expose] def Ext (w : List (α × Op n Γ)) (i : Fin n) (q r : ℕ) : Prop :=
  q < r ∧ IsHolePushOn w i r ∧ WellNested (w.extract (q + 1) r)

theorem IsPushOn.lt_length {i : Fin n} {r : ℕ} (h : IsPushOn w i r) : r < w.length := by
  obtain ⟨a, γ, h⟩ := h
  exact (List.getElem?_eq_some_iff.mp h).1

/-- Only the least extension of a push is an extension: a later one would enclose it in a
well-nested factor. -/
theorem Ext.eq_of_le {i : Fin n} {q r r' : ℕ} (h : Ext w i q r) (h' : Ext w i q r')
    (hle : r ≤ r') : r = r' := by
  by_contra hne
  obtain ⟨hqr, ⟨hpush, hnot⟩, -⟩ := h
  obtain ⟨hqr', ⟨hpush', -⟩, hwn'⟩ := h'
  obtain ⟨-, -, -, hwm⟩ := exists_matches_of_wellNested hwn'
    (by have := hpush'.lt_length; omega) (show q + 1 ≤ r by omega)
    (by omega) hpush
  exact hnot hwm

/-- The greedy chain from position `q`, oldest first: `q`, then the least extension, and so on. -/
noncomputable def chainFrom (w : List (α × Op n Γ)) (i : Fin n) (q : ℕ) : List ℕ :=
  if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q]
termination_by w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

theorem chainFrom_eq {i : Fin n} {q : ℕ} : chainFrom w i q =
    if h : ∃ r, Ext w i q r then q :: chainFrom w i (Nat.find h) else [q] := by
  rw [chainFrom]

theorem mem_chainFrom_self {i : Fin n} {q : ℕ} : q ∈ chainFrom w i q := by
  rw [chainFrom_eq]
  split_ifs <;> simp

/-- Every element of the greedy chain after `q` is a hole push of stack `i`, and the elements
increase. -/
theorem chainFrom_spec {i : Fin n} :
    ∀ q, ∀ r ∈ chainFrom w i q, q ≤ r ∧ (r ≠ q → IsHolePushOn w i r)
  | q, r, hr => by
    rw [chainFrom_eq] at hr
    split_ifs at hr with h
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨le_rfl, fun h' => absurd rfl h'⟩
      · have hspec := Nat.find_spec h
        obtain ⟨hle, hhole⟩ := chainFrom_spec (Nat.find h) r hr
        refine ⟨by have := hspec.1; omega, fun _ => ?_⟩
        by_cases hrf : r = Nat.find h
        · rw [hrf]
          exact hspec.2.1
        · exact hhole hrf
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨le_rfl, fun h' => absurd rfl h'⟩
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

/-- **Greedy chains are closed under extension**: an extension of an element of the chain is in
the chain. -/
theorem mem_chainFrom_of_ext {i : Fin n} : ∀ q, ∀ p ∈ chainFrom w i q, ∀ r, Ext w i p r →
    r ∈ chainFrom w i q
  | q, p, hp, r, hr => by
    rw [chainFrom_eq] at hp ⊢
    split_ifs at hp ⊢ with h
    · rcases List.mem_cons.mp hp with rfl | hp
      · -- The least extension is the only one.
        have hmin := Nat.find_min' h hr
        obtain rfl := (Nat.find_spec h).eq_of_le hr hmin
        exact List.mem_cons_of_mem _ mem_chainFrom_self
      · exact List.mem_cons_of_mem _ (mem_chainFrom_of_ext (Nat.find h) p hp r hr)
    · obtain rfl := List.mem_singleton.mp hp
      exact absurd ⟨r, hr⟩ h
termination_by q => w.length - q
decreasing_by
  have hspec := Nat.find_spec h
  have := hspec.2.1.1.lt_length
  have := hspec.1
  omega

end Chains

end Cslib.Automata.MPDA
