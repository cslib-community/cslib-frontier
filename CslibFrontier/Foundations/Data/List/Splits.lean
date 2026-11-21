/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import CslibFrontier.Foundations.Data.List.Extract

/-!
# Bounded splittings of a list

`List.Splits P K w` says that `w` is the concatenation of at most `K` factors satisfying `P`.
Restricted classes of runs of multistack pushdown automata are of this form: a sequence with at
most `K` contexts splits into at most `K` factors that each use at most one stack.

## Main results

* `List.Splits.trans`: a splitting into `K` factors that each split into `m` factors gives a
  splitting into `K * m` factors.
* `List.Splits.of_isInfix`: for an infix-closed `P`, an infix of a splittable list splits with
  the same bound.
* `List.Splits.card_le`: for an infix-closed `P`, a set of positions no two of which lie in a
  common factor satisfying `P` has at most as many elements as there are factors.
-/

public section

namespace List

variable {β : Type*}

/-- `Splits P K w` holds when `w` is the concatenation of at most `K` factors satisfying `P`. -/
@[expose] def Splits (P : List β → Prop) (K : ℕ) (w : List β) : Prop :=
  ∃ ws : List (List β), ws.length ≤ K ∧ ws.flatten = w ∧ ∀ v ∈ ws, P v

namespace Splits

variable {P Q : List β → Prop} {K K' : ℕ} {w : List β}

/-- A splitting into at most `K` factors is one into at most `K'` factors for `K ≤ K'`. -/
theorem mono_bound (h : Splits P K w) (hK : K ≤ K') : Splits P K' w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen.trans hK, hw, hP⟩

/-- A splitting into factors satisfying `P` is one into factors satisfying a weaker `Q`. -/
theorem mono (h : Splits P K w) (hPQ : ∀ v, P v → Q v) : Splits Q K w :=
  let ⟨ws, hlen, hw, hP⟩ := h
  ⟨ws, hlen, hw, fun v hv => hPQ v (hP v hv)⟩

private theorem flatten_of_forall {m : ℕ} :
    ∀ ws : List (List β), (∀ v ∈ ws, Splits P m v) → Splits P (ws.length * m) ws.flatten
  | [], _ => ⟨[], Nat.zero_le _, rfl, by simp⟩
  | v :: ws, h => by
    obtain ⟨us, hlen, rfl, hP⟩ := h v mem_cons_self
    obtain ⟨us', hlen', hw', hP'⟩ :=
      flatten_of_forall ws fun v hv => h v (mem_cons_of_mem _ hv)
    refine ⟨us ++ us', ?_, ?_, ?_⟩
    · rw [length_append, length_cons, Nat.succ_mul]
      omega
    · rw [flatten_append, hw', flatten_cons]
    · intro u hu
      rcases mem_append.mp hu with hu | hu
      · exact hP u hu
      · exact hP' u hu

/-- A splitting into factors that themselves split boundedly gives a bounded splitting. -/
theorem trans {m : ℕ} (h : Splits (Splits P m) K w) : Splits P (K * m) w := by
  obtain ⟨ws, hlen, rfl, hP⟩ := h
  exact (flatten_of_forall ws hP).mono_bound (Nat.mul_le_mul_right m hlen)

private theorem prefix_aux (hP : ∀ u v, u <+: v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <+: ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (prefix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [flatten_cons] at ht
    rcases append_eq_append_iff.mp ht with ⟨a, rfl, -⟩ | ⟨c, rfl, hc⟩
    · exact ⟨[u], by simp, by simp,
        by simpa using hP u (u ++ a) (prefix_append u a) (hws _ mem_cons_self)⟩
    · obtain ⟨us, hlen, rfl, hus⟩ := prefix_aux hP ws c
        (fun v hv => hws v (mem_cons_of_mem _ hv)) ⟨t, hc.symm⟩
      refine ⟨v :: us, by simpa using hlen, by simp, ?_⟩
      intro x hx
      rcases mem_cons.mp hx with rfl | hx
      · exact hws _ mem_cons_self
      · exact hus x hx

private theorem suffix_aux (hP : ∀ u v, u <:+ v → P v → P u) :
    ∀ (ws : List (List β)) (u : List β), (∀ v ∈ ws, P v) → u <:+ ws.flatten →
      ∃ us : List (List β), us.length ≤ ws.length ∧ us.flatten = u ∧ ∀ v ∈ us, P v
  | [], u, _, hu => ⟨[], le_rfl, (suffix_nil.mp hu).symm, by simp⟩
  | v :: ws, u, hws, ⟨t, ht⟩ => by
    rw [flatten_cons] at ht
    rcases append_eq_append_iff.mp ht with ⟨a, rfl, rfl⟩ | ⟨c, rfl, hc⟩
    · refine ⟨a :: ws, by simp, by simp, ?_⟩
      intro x hx
      rcases mem_cons.mp hx with rfl | hx
      · exact hP x (t ++ x) (suffix_append t x) (hws _ mem_cons_self)
      · exact hws x (mem_cons_of_mem _ hx)
    · obtain ⟨us, hlen, rfl, hus⟩ := suffix_aux hP ws u
        (fun v hv => hws v (mem_cons_of_mem _ hv)) ⟨c, hc.symm⟩
      exact ⟨us, by simp only [length_cons]; omega, rfl, hus⟩

/-- If `P` is closed under taking infixes, so is having a splitting into at most `K` factors
satisfying `P`. -/
theorem of_isInfix (hP : ∀ u v, u <:+: v → P v → P u) (h : Splits P K w) {u : List β}
    (hu : u <:+: w) : Splits P K u := by
  obtain ⟨ws, hlen, rfl, hws⟩ := h
  obtain ⟨t, ht, hts⟩ := infix_iff_prefix_suffix.mp hu
  obtain ⟨vs, hvlen, rfl, hvs⟩ :=
    suffix_aux (fun u v h => hP u v h.isInfix) ws t hws hts
  obtain ⟨us, hulen, rfl, hus⟩ :=
    prefix_aux (fun u v h => hP u v h.isInfix) vs _ hvs ht
  exact ⟨us, (hulen.trans hvlen).trans hlen, rfl, hus⟩

private theorem card_le_aux (hP : ∀ u v, u <:+: v → P v → P u) :
    ∀ ws : List (List β), (∀ v ∈ ws, P v) → ∀ T : Finset ℕ,
      (∀ t ∈ T, t < ws.flatten.length) →
      (∀ t ∈ T, ∀ t' ∈ T, t < t' → ¬P (ws.flatten.extract t (t' + 1))) → T.card ≤ ws.length
  | [], _, T, hT, _ => by
    rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun t ht => by
      simpa using hT t ht)]
    simp
  | v :: ws, hws, T, hT, hTP => by
    rw [flatten_cons] at hT hTP
    rw [← Finset.card_filter_add_card_filter_not (p := fun t => t < v.length), length_cons]
    suffices h : (T.filter fun t => t < v.length).card ≤ 1 ∧
        (T.filter fun t => ¬t < v.length).card ≤ ws.length by omega
    refine ⟨?_, ?_⟩
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      by_contra hab
      wlog hlt : a < b generalizing a b
      · exact this b a hb ha (Ne.symm hab) (by omega)
      apply hTP a ha.1 b hb.1 hlt
      rw [extract_append_right _ _ (by omega)]
      exact hP _ _ (extract_isInfix v _ _) (hws v mem_cons_self)
    · have hinj : Set.InjOn (fun t => t - v.length)
          (T.filter fun t => ¬t < v.length : Finset ℕ) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
      rw [← Finset.card_image_of_injOn hinj]
      refine card_le_aux hP ws (fun u hu => hws u (mem_cons_of_mem _ hu)) _ ?_ ?_
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        simp only [Finset.mem_filter] at hs
        have := hT s hs.1
        simp only [length_append] at this
        omega
      · intro t ht t' ht' hlt
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht'
        simp only [Finset.mem_filter] at hs hs'
        have := hTP s hs.1 s' hs'.1 (by omega)
        rwa [show s = v.length + (s - v.length) by omega,
          show s' + 1 = v.length + (s' - v.length + 1) by omega,
          extract_append_left] at this

/-- If `w` splits into at most `K` factors satisfying an infix-closed `P`, then every set `T` of
positions of `w` such that no two of them lie in a common factor satisfying `P` has at most `K`
elements. -/
theorem card_le (hP : ∀ u v, u <:+: v → P v → P u) (h : Splits P K w) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t < w.length)
    (hTP : ∀ t ∈ T, ∀ t' ∈ T, t < t' → ¬P (w.extract t (t' + 1))) : T.card ≤ K := by
  obtain ⟨ws, hlen, rfl, hws⟩ := h
  exact (card_le_aux hP ws hws T hT hTP).trans hlen

end Splits

end List
