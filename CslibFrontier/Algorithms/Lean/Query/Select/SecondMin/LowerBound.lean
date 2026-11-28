/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Spec
public import Mathlib.Data.Nat.Log
import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Certificate
import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Trace
import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.Adversary

/-!
# The comparison lower bound for finding the second smallest

For every list of `n ≥ 2` distinct keys and every correct second-minimum algorithm, some linear
order forces at least `n + ⌈log₂ n⌉ − 2` comparisons. The program can compare arbitrary keys of
the ambient type, including keys outside the input.

Whenever two undefeated input keys meet, the adversary favors the one with more wins over
previously undefeated keys. Moving the chosen winner to the bottom of the current order preserves
all earlier answers. The terminal certificate for the comparison transcript then supplies the
predecessors needed for the counting bound.
-/

public section

namespace Cslib.Query

open SecondMin

variable {α : Type}

open Classical in
/-- Record the smaller key first, irrespective of the order in which the query was asked. -/
private noncomputable def orient (r : α → α → Prop) (p : α × α) : α × α :=
  if r p.1 p.2 then p else p.swap

private theorem map_orient_congr {r s : α → α → Prop} {T : List (α × α)} (h : AgreeOn r s T) :
    T.map (orient r) = T.map (orient s) := by
  apply List.map_congr_left
  rintro ⟨a, b⟩ hab
  by_cases hr : r a b
  · simp [orient, hr, (h.iff hab).mp hr]
  · simp [orient, hr, mt (h.iff hab).mpr hr]

private theorem lost_of_foundAbove {r : α → α → Prop} {T : List (α × α)} {x : α}
    (h : FoundAbove r T x) : Lost (T.map (orient r)) x := by
  obtain ⟨a, b, hab, hne, (⟨rfl, hr⟩ | ⟨rfl, hr⟩)⟩ := foundAbove_iff.mp h
  · exact ⟨a, hne, by simpa [orient, hr] using List.mem_map_of_mem (f := orient r) hab⟩
  · exact ⟨b, hne.symm, by simpa [orient, hr] using List.mem_map_of_mem (f := orient r) hab⟩

private theorem mem_orient_of_observed {r : α → α → Prop} [IsLinearOrder α r]
    {T : List (α × α)} {w x : α} (h : ObservedBefore r T w x) : (w, x) ∈ T.map (orient r) := by
  obtain ⟨hne, hr, hT | hT⟩ := h
  · simpa [orient, hr] using List.mem_map_of_mem (f := orient r) hT
  · have hn : ¬ r x w := fun hx => hne (antisymm hr hx)
    simpa [orient, hn] using List.mem_map_of_mem (f := orient r) hT

private theorem exists_step (S : Finset α) (r : α → α → Prop) [IsLinearOrder α r]
    (T : List (α × α)) (hT : Trace S (T.map (orient r))) (a b : α) :
    ∃ s, IsLinearOrder α s ∧ AgreeOn r s T ∧ Trace S ((T ++ [(a, b)]).map (orient s)) := by
  classical
  let E := T.map (orient r)
  let fresh (x : α) := x ∈ S ∧ ¬ Lost E x
  have unchanged {w l : α} (hp : orient r (a, b) = (w, l)) (cannot : w ≠ l → ¬ fresh l) :
      ∃ s, IsLinearOrder α s ∧ AgreeOn r s T ∧ Trace S ((T ++ [(a, b)]).map (orient s)) := by
    refine ⟨r, inferInstance, AgreeOn.refl r T, ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, hp]
    exact hT.snoc w l fun hne hl hnl => (cannot hne ⟨hl, hnl⟩).elim
  rcases eq_or_ne a b with rfl | hab
  · exact unchanged (w := a) (l := a) (by simp [orient, refl_of r a]) fun h => (h rfl).elim
  have lower (w l : α) (hwl : w ≠ l) (hw : fresh w)
      (hd : fresh l → firstWins S E l ≤ firstWins S E w)
      (hquery : (a, b) = (w, l) ∨ (a, b) = (l, w)) :
      ∃ s, IsLinearOrder α s ∧ AgreeOn r s T ∧ Trace S ((T ++ [(a, b)]).map (orient s)) := by
    let s := moveToBot r w
    have hkeep : AgreeOn r s T := agreeOn_moveToBot (mt lost_of_foundAbove hw.2)
    have hp : orient s (a, b) = (w, l) := by
      rcases hquery with h | h <;> rw [h] <;> simp [orient, s, moveToBot_iff, hwl.symm]
    refine ⟨s, isLinearOrder_moveToBot r w, hkeep, ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, hp, ← map_orient_congr hkeep]
    exact hT.snoc w l fun _ hl hnl => ⟨hw.1, hw.2, hd ⟨hl, hnl⟩⟩
  by_cases ha : fresh a <;> by_cases hb : fresh b
  · rcases le_total (firstWins S E a) (firstWins S E b) with h | h
    · exact lower b a hab.symm hb (fun _ => h) (.inr rfl)
    · exact lower a b hab ha (fun _ => h) (.inl rfl)
  · exact lower a b hab ha (fun h => (hb h).elim) (.inl rfl)
  · exact lower b a hab.symm hb (fun h => (ha h).elim) (.inr rfl)
  · by_cases hr : r a b
    · exact unchanged (w := a) (l := b) (by simp [orient, hr]) fun _ => hb
    · exact unchanged (w := b) (l := a) (by simp [orient, hr]) fun _ => ha

/-- For every correct second-smallest algorithm and every list of `n ≥ 2` distinct keys, there
is a linear order whose comparison oracle forces at least `n + ⌈log₂ n⌉ − 2` queries. -/
theorem IsSecondMinAlg.exists_le_countQueries {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsSecondMinAlg alg) {xs : List α} (hxs : xs.Nodup) (hn : 2 ≤ xs.length) :
    ∃ f : α → α → Bool, IsLinearOrder α (fun a b => f a b = true) ∧
      xs.length + Nat.clog 2 xs.length - 2 ≤ (alg xs).countQueries (LEQuery.oracleOf f) := by
  classical
  let S := xs.toFinset
  obtain ⟨f, hr, htrace⟩ := LEQuery.exists_adversary_run (alg xs)
    (fun r T => Trace S (T.map (orient r))) (fun _ _ => .nil)
    (fun r _ T hT a b => exists_step S r T hT a b)
  refine ⟨f, hr, ?_⟩
  let r a b := f a b = true
  let oracle : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf f
  let Q := LEQuery.queriedPairs oracle (alg xs)
  have hE : Trace S (Q.map (orient r)) := htrace
  have hcard : S.card = xs.length := List.toFinset_card_of_nodup hxs
  obtain ⟨m, hm, hroot⟩ := hE.exists_unbeaten (Finset.card_pos.mp (by omega))
  obtain ⟨y, -, hall, hother⟩ := halg.predecessors_of_undefeated r oracle
    (fun _ _ => by simp [oracle, r]) hxs hn (List.mem_toFinset.mp hm)
    fun w h => hroot ⟨w, h.1, mem_orient_of_observed h⟩
  have hcount := hE.lowerBound (second := y) hm hroot (fun x hx hxm => by
    obtain ⟨w, hw⟩ := hall x (List.mem_toFinset.mp hx) hxm
    exact ⟨w, hw.1, mem_orient_of_observed hw⟩) (fun x hx hxm hxy => by
    obtain ⟨w, hwm, hw⟩ := hother x (List.mem_toFinset.mp hx) hxm hxy
    exact ⟨w, hwm, hw.1, mem_orient_of_observed hw⟩)
  simpa only [hcard, List.length_map, Q, LEQuery.length_queriedPairs] using hcount

end Cslib.Query
