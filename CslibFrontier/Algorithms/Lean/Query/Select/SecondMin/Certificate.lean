/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Spec
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.Fooling
import Mathlib.Data.List.Nodup

/-!
# Comparison certificates for the second smallest key

If `m` has never lost a comparison, the transcript is consistent with `m` coming first.
Any other input key `c` that has lost only to `m` can then be put second without changing any
answer. A correct algorithm must return `c` on that transcript. Consequently every input key
other than `m` has a predecessor, and every key other than `m` and the reported second key has
a predecessor different from `m`. Comparisons against keys outside the input are allowed.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- A comparison in `T`, in either query orientation, puts `w` strictly before `x`
under the linear order `r`. -/
@[expose] def SecondMin.ObservedBefore (r : α → α → Prop) (T : List (α × α)) (w x : α) : Prop :=
  w ≠ x ∧ r w x ∧ ((w, x) ∈ T ∨ (x, w) ∈ T)

open SecondMin

private theorem agreeOn_first_two {r : α → α → Prop} [IsLinearOrder α r]
    {T : List (α × α)} {m c : α} (hm : ∀ w, ¬ ObservedBefore r T w m)
    (hc : ∀ w, ObservedBefore r T w c → w = m) :
    ∀ a b, (a, b) ∈ T → (r a b ↔ moveToBot (moveToBot r c) m a b) := by
  have := isLinearOrder_moveToBot r c
  have := isLinearOrder_moveToBot (moveToBot r c) m
  have keep {a b : α} (h : ObservedBefore r T a b) : moveToBot (moveToBot r c) m a b := by
    rcases eq_or_ne a m with rfl | ham
    · exact moveToBot_bot _ _ _
    · exact moveToBot_iff.mpr (.inr ⟨fun e => hm a (e ▸ h),
        moveToBot_iff.mpr (.inr ⟨fun e => ham (hc a (e ▸ h)), h.2.1⟩)⟩)
  intro a b hab
  rcases eq_or_ne a b with rfl | hne
  · exact ⟨fun _ => refl_of _ a, fun _ => refl_of _ a⟩
  · refine ⟨fun h => keep ⟨hne, h, .inl hab⟩, fun h => ?_⟩
    by_contra h'
    exact hne (antisymm h (keep ⟨hne.symm, (total_of r a b).resolve_left h', .inr hab⟩))

open Classical in
private theorem second_of_first_two (r : α → α → Prop) {xs : List α} {m c : α}
    (hxs : xs.Nodup) (hm : m ∈ xs) (hc : c ∈ xs) (hne : c ≠ m) :
    xs.IsOrderStatistic (moveToBot (moveToBot r c) m) 1 c := by
  refine ⟨hc, ?_, ?_⟩
  · calc
      _ = xs.count m := by
        rw [List.count_eq_countP]
        exact List.countP_congr fun x _ => by simp [moveToBot_iff, hne]
      _ ≤ 1 := List.nodup_iff_count_le_one.mp hxs m
  · have perm := (List.perm_cons_erase hm).trans
      ((List.perm_cons_erase ((List.mem_erase_of_ne hne).mpr hc)).cons m)
    rw [perm.countP_eq]
    simp [moveToBot_iff, hne, hne.symm]

private theorem eval_eq_second_of_predecessors {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsSecondMinAlg alg) (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs.Nodup) (hn : 2 ≤ xs.length) {m c : α} (hm : m ∈ xs) (hc : c ∈ xs)
    (hne : c ≠ m) (hfirst : ∀ w, ¬ ObservedBefore r (LEQuery.queriedPairs oracle (alg xs)) w m)
    (hsecond : ∀ w, ObservedBefore r (LEQuery.queriedPairs oracle (alg xs)) w c → w = m) :
    (alg xs).eval oracle = some c := by
  classical
  let r' := moveToBot (moveToBot r c) m
  have := isLinearOrder_moveToBot r c
  have : IsLinearOrder α r' := isLinearOrder_moveToBot _ m
  let alt : {ι : Type} → LEQuery α ι → ι := LEQuery.oracleOf fun a b => decide (r' a b)
  have agree := agreeOn_first_two hfirst hsecond
  obtain ⟨y, hy, hrank⟩ := halg.correct r' alt (fun _ _ => rfl) xs hxs hn
  have heval := LEQuery.eval_eq_of_agree oracle alt (alg xs) fun a b hab => by
    rw [horacle]
    exact decide_eq_decide.mpr (agree a b hab)
  rw [← heval, hy, hrank.unique (second_of_first_two r hxs hm hc hne)]

/-- In a terminal transcript of a correct second-minimum algorithm, if `m` has no observed
predecessor then every other input key does. Apart from `m` and the output, each key has an
observed predecessor distinct from `m`. -/
theorem IsSecondMinAlg.predecessors_of_undefeated {alg : List α → FreeM (LEQuery α) (Option α)}
    (halg : IsSecondMinAlg alg) (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs.Nodup) (hn : 2 ≤ xs.length) {m : α} (hm : m ∈ xs)
    (hfirst : ∀ w, ¬ ObservedBefore r (LEQuery.queriedPairs oracle (alg xs)) w m) :
    let T := LEQuery.queriedPairs oracle (alg xs)
    ∃ y, (alg xs).eval oracle = some y ∧
      (∀ x ∈ xs, x ≠ m → ∃ w, ObservedBefore r T w x) ∧
      (∀ x ∈ xs, x ≠ m → x ≠ y → ∃ w, w ≠ m ∧ ObservedBefore r T w x) := by
  classical
  let T := LEQuery.queriedPairs oracle (alg xs)
  obtain ⟨y, hy, -⟩ := halg.correct r oracle horacle xs hxs hn
  have force {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hne : b ≠ a)
      (h₁ : ∀ w, ¬ ObservedBefore r T w a) (h₂ : ∀ w, ObservedBefore r T w b → w = a) :
      y = b := Option.some.inj <| hy.symm.trans
        (eval_eq_second_of_predecessors halg r oracle horacle hxs hn ha hb hne h₁ h₂)
  refine ⟨y, hy, fun x hx hxm => ?_, fun x hx hxm hxy => ?_⟩
  · by_contra! hnone
    have hyx := force hm hx hxm hfirst fun w h => (hnone w h).elim
    have hym := force hx hm hxm.symm hnone fun w h => (hfirst w h).elim
    exact hxm (hyx.symm.trans hym)
  · by_contra! hnone
    exact hxy (force hm hx hxm hfirst fun w h => by by_contra hw; exact hnone w hw h).symm

end Cslib.Query
