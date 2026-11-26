/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Symmetric
import CslibFrontier.Foundations.Probability.InfinitePi

/-!
# Lopsided Moser–Tardos algorithmic local lemma

This module proves **Section 6** of [MoserTardos2010] (Theorem 6.1 and Lemma 6.2), replacing the
variable-sharing dependency graph `Adj vbl` with the *lopsidependency* graph `Lopsidependent`:
two events `A i` and `A j` are lopsidependent if there exist assignments `f` and `g` agreeing
outside `vbl i ∩ vbl j` such that `f ∈ A i`, `g ∈ A j`, and either `f ∉ A j` or `g ∉ A i`.
Disjoint variable sets are never lopsidependent (`not_lopsidependent_of_disjoint`), so the
lopsided local lemma weakens the hypothesis and strictly generalizes Theorem 1.2.

## Main definitions

* `Cslib.Probability.MoserTardos.Lopsidependent`: lopsidependence of two events depending on
  `vbl i` and `vbl j`.
* `Cslib.Probability.MoserTardos.lopsidedAdj`: reflexive closure `i = j ∨ Lopsidependent vbl A i j`.

## Main results

* `Cslib.Probability.MoserTardos.Lopsided.table_witness_le`: **Lemma 6.2** of [MoserTardos2010],
  bounding the probability that a fixed structure occurs as a lopsided witness structure by
  `∏ p ∈ S, Pr[A p.1]`, proved by normalizing the log into a canonical depth-ordered log using the
  commutation of non-lopsidependent consecutive resamplings.
* `Cslib.Probability.MoserTardos.Lopsided.lintegral_resamplings_le`,
  `Cslib.Probability.MoserTardos.Lopsided.lintegral_sum_resamplings_le`,
  `Cslib.Probability.MoserTardos.Lopsided.ae_exists_forall_notMem_run`,
  `Cslib.Probability.MoserTardos.Lopsided.exists_forall_notMem`: **Theorem 6.1** of
  [MoserTardos2010] (asymmetric form) and its symmetric specialization (`*_symmetric`).

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010, Section 6]
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Cslib.Probability.MoserTardos

section Lopsidependent

variable {V ι : Type*} {α : V → Type*}

/-- Events `A i` and `A j` are *lopsidependent* [MoserTardos2010, Section 6] when there exist
assignments `f` and `g` differing only on `vbl i ∩ vbl j` such that `f ∈ A i`, `g ∈ A j`, and
either `f ∉ A j` or `g ∉ A i`. -/
def Lopsidependent [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i j : ι) : Prop :=
  ∃ f g : ∀ v, α v, (∀ v, v ∉ vbl i ∩ vbl j → f v = g v) ∧
    f ∈ A i ∧ g ∈ A j ∧ (f ∉ A j ∨ g ∉ A i)

theorem lopsidependent_iff [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : Lopsidependent vbl A i j ↔
      ∃ f g : ∀ v, α v, (∀ v, v ∉ vbl i ∩ vbl j → f v = g v) ∧
        f ∈ A i ∧ g ∈ A j ∧ (f ∉ A j ∨ g ∉ A i) := by
  rw [Lopsidependent]

theorem lopsidependent_comm [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : Lopsidependent vbl A i j ↔ Lopsidependent vbl A j i := by
  suffices ∀ {a b}, Lopsidependent vbl A a b → Lopsidependent vbl A b a from ⟨this, this⟩
  rintro a b ⟨f, g, hfg, hfi, hgj, hne⟩
  exact ⟨g, f, fun v hv => (hfg v (inter_comm (vbl b) (vbl a) ▸ hv)).symm, hgj, hfi, hne.symm⟩

theorem not_lopsidependent_of_disjoint [DecidableEq V] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) {i j : ι} (hd : Disjoint (vbl i) (vbl j)) :
    ¬Lopsidependent vbl A i j := by
  rintro ⟨f, g, hfg, hfi, hgj, hne⟩
  obtain rfl : f = g := funext fun v => hfg v (by simp [disjoint_iff_inter_eq_empty.1 hd])
  exact hne.elim (· hgj) (· hfi)

/-- Reflexive lopsidependency relation `i = j ∨ Lopsidependent vbl A i j`. -/
def lopsidedAdj [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i j : ι) : Prop :=
  i = j ∨ Lopsidependent vbl A i j

theorem lopsidedAdj_iff [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : lopsidedAdj vbl A i j ↔ i = j ∨ Lopsidependent vbl A i j := by
  rw [lopsidedAdj]

theorem lopsidedAdj_refl [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i : ι) : lopsidedAdj vbl A i i :=
  Or.inl rfl

theorem lopsidedAdj_comm [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : lopsidedAdj vbl A i j ↔ lopsidedAdj vbl A j i := by
  simp only [lopsidedAdj, eq_comm, lopsidependent_comm]

end Lopsidependent

section CanonicalLog

variable {V ι : Type*} [DecidableEq V] {α : V → Type*} (vbl : ι → Finset V)

private theorem uses_cons_swap (u v : List ι) (a b : ι) (x : V) :
    uses vbl (u ++ a :: b :: v) x = uses vbl (u ++ b :: a :: v) x := by
  induction u with
  | nil => simp only [List.nil_append, uses_cons]; omega
  | cons c u ih => simp only [List.cons_append, uses_cons, ih]

private theorem current_append_swap (T : ∀ p : V × ℕ, α p.1) (u v : List ι) (a b : ι) :
    current vbl T (u ++ a :: b :: v) = current vbl T (u ++ b :: a :: v) :=
  funext fun x => by rw [current_apply, current_apply, uses_cons_swap]

private theorem isLog_swap_cons {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    {a b : ι} (hab : ¬Lopsidependent vbl A a b) {v : List ι}
    (h : IsLog vbl A T (a :: b :: v)) : IsLog vbl A T (b :: a :: v) := by
  rw [isLog_cons, isLog_cons] at h ⊢
  rcases h with ⟨hg, hf, hv⟩
  let f := current vbl T v
  let g := current vbl T (b :: v)
  let φ := current vbl T (a :: v)
  let hfn : ∀ x, α x := fun x => if x ∈ vbl a ∩ vbl b then g x else f x
  have h_eq_f : ∀ x, x ∉ vbl a ∩ vbl b → hfn x = f x := fun x hx => ite_eq_right hx
  have h_eq_g : ∀ x ∈ (vbl a : Set V), hfn x = g x := fun x hx => by
    by_cases hxb : x ∈ vbl b
    · simp [hfn, Finset.mem_coe.1 hx, hxb]
    · simp only [hfn, f, g, hxb, mem_inter, and_false, ↓reduceIte, current_apply]
      rw [uses_cons, ite_eq_right hxb, add_zero]
  have ha_hfn : hfn ∈ A a := (hA a h_eq_g).mpr hg
  have hnot : ¬(hfn ∉ A b ∨ f ∉ A a) := fun hbad => hab ⟨hfn, f, h_eq_f, ha_hfn, hf, hbad⟩
  rw [not_or, not_not, not_not] at hnot
  have h_eq_φ : ∀ x ∈ (vbl b : Set V), hfn x = φ x := fun x hx => by
    have hxb := Finset.mem_coe.1 hx
    by_cases hxa : x ∈ vbl a <;>
      simp only [hfn, f, g, φ, hxa, hxb, mem_inter, and_self, false_and, ↓reduceIte, current_apply]
    · rw [uses_cons, uses_cons, ite_eq_left hxb, ite_eq_left hxa]
    · rw [uses_cons, ite_eq_right hxa, add_zero]
  exact ⟨(hA b h_eq_φ).mp hnot.1, hnot.2, hv⟩

private theorem isLog_swap {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    {a b : ι} (hab : ¬Lopsidependent vbl A a b) :
    ∀ u v : List ι, IsLog vbl A T (u ++ a :: b :: v) → IsLog vbl A T (u ++ b :: a :: v)
  | [], v, h => isLog_swap_cons vbl hA hab h
  | c :: u, v, h => by
    rw [List.cons_append, isLog_cons] at h ⊢
    rw [← current_append_swap vbl T u v a b]
    exact ⟨h.1, isLog_swap hA hab u v h.2⟩

private noncomputable def canonList (S : Finset (ι × ℕ)) : List ι :=
  (S.toList.mergeSort (fun a b => decide (a.2 ≤ b.2))).map Prod.fst

section Trace

variable (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]

private def foldPush (S₀ : Finset (ι × ℕ)) (w : List ι) : Finset (ι × ℕ) :=
  w.foldl (fun S j => pushRel R j S) S₀

private theorem foldPush_append (S₀ : Finset (ι × ℕ)) (u v : List ι) :
    foldPush R S₀ (u ++ v) = foldPush R (foldPush R S₀ u) v := by
  simp [foldPush, List.foldl_append]

private theorem witnessRel_eq_foldPush (i : ι) (w : List ι) :
    witnessRel R i w = foldPush R {(i, 0)} w :=
  rfl

private def traceSteps (S₀ : Finset (ι × ℕ)) : List ι → List (Option (ι × ℕ))
  | [] => []
  | j :: w =>
    let l := levelRel R j S₀
    if l = 0 then none :: traceSteps S₀ w
    else some (j, l) :: traceSteps (insert (j, l) S₀) w

private theorem traceSteps_length (S₀ : Finset (ι × ℕ)) (w : List ι) :
    (traceSteps R S₀ w).length = w.length := by
  induction w generalizing S₀ with
  | nil => simp [traceSteps]
  | cons j w ih =>
    simp only [traceSteps]
    split_ifs <;> simp [ih]

private theorem traceSteps_append (S₀ : Finset (ι × ℕ)) (u v : List ι) :
    traceSteps R S₀ (u ++ v) = traceSteps R S₀ u ++ traceSteps R (foldPush R S₀ u) v := by
  induction u generalizing S₀ with
  | nil => simp [traceSteps, foldPush]
  | cons j u ih =>
    simp only [List.cons_append, traceSteps, foldPush, List.foldl_cons]
    by_cases h0 : levelRel R j S₀ = 0
    · simp only [h0, ↓reduceIte, List.cons_append, pushRel_of_eq_zero h0]
      exact congrArg (none :: ·) (ih S₀)
    · simp only [h0, ↓reduceIte, List.cons_append, pushRel_of_ne_zero h0]
      exact congrArg (some (j, levelRel R j S₀) :: ·) (ih (insert (j, levelRel R j S₀) S₀))

private theorem traceSteps_swap (hRs : ∀ {i j}, R i j → R j i) (S₀ : Finset (ι × ℕ))
    {a b : ι} {p : ι × ℕ} {o : Option (ι × ℕ)}
    (hst : traceSteps R S₀ [a, b] = [some p, o])
    (ho : o = none ∨ ∃ q : ι × ℕ, o = some q ∧ q.2 ≤ p.2) :
    ¬R a b ∧ traceSteps R S₀ [b, a] = [o, some p] ∧
      foldPush R S₀ [b, a] = foldPush R S₀ [a, b] := by
  by_cases ha0 : levelRel R a S₀ = 0
  · simp [traceSteps, ha0] at hst
  simp only [traceSteps, ha0, ↓reduceIte, List.cons.injEq, Option.some.injEq] at hst
  obtain ⟨rfl, hst⟩ := hst
  set la := levelRel R a S₀
  set S₁ := insert (a, la) S₀
  have hnab : ¬R a b := by
    intro hab
    have hlt := lt_levelRel (mem_insert_self (a, la) S₀) hab
    have hb0 : levelRel R b S₁ ≠ 0 := ((Nat.zero_le la).trans_lt hlt).ne'
    rcases ho with rfl | ⟨q, rfl, hle⟩
    · simp [hb0] at hst
    · have hq : (b, levelRel R b S₁) = q :=
        Option.some.inj ((List.cons.inj (by simpa only [hb0, ↓reduceIte] using hst)).1)
      exact (not_lt_of_ge hle) ((congrArg Prod.snd hq) ▸ hlt)
  have hnba : ¬R b a := fun h => hnab (hRs h)
  have hb := levelRel_insert_of_not_rel hnab la S₀
  have ha (k : ℕ) := levelRel_insert_of_not_rel hnba k S₀
  refine ⟨hnab, ?_, (pushRel_comm_of_not_rel hnba hnab S₀).symm⟩
  by_cases hb0 : levelRel R b S₀ = 0 <;>
    simp only [S₁, hb, hb0, ↓reduceIte, List.cons.injEq] at hst <;>
    simp [traceSteps, hb0, ha0, ha, la, ← hst.1]

private theorem traceSteps_map_some_eq (hRr : ∀ i, R i i) :
    ∀ (S₀ : Finset (ι × ℕ)) (w : List ι) (L : List (ι × ℕ)),
      traceSteps R S₀ w = L.map some →
      w = L.map Prod.fst ∧ L.Nodup ∧ (∀ p ∈ L, p ∉ S₀) ∧
        foldPush R S₀ w = S₀ ∪ L.toFinset
  | S₀, [], [], _ => by simp [foldPush]
  | S₀, [], p :: L, h => by simp [traceSteps] at h
  | S₀, j :: w, [], h => by cases h0 : levelRel R j S₀ <;> simp [traceSteps, h0] at h
  | S₀, j :: w, p :: L, h => by
    simp only [traceSteps] at h
    split_ifs at h with h0
    · simp at h
    · rcases List.cons.inj h with ⟨hp, hw⟩
      obtain rfl := Option.some.inj hp
      obtain ⟨hwm, hnodup, hnot, hfold⟩ :=
        traceSteps_map_some_eq hRr (insert (j, levelRel R j S₀) S₀) w L hw
      refine ⟨by simp [hwm], List.nodup_cons.2 ⟨fun hm => hnot _ hm (mem_insert_self _ _), hnodup⟩,
        List.forall_mem_cons.2 ⟨levelRel_notMem hRr j S₀,
          fun q hq hm => hnot q hq (mem_insert_of_mem hm)⟩, ?_⟩
      rw [foldPush, List.foldl_cons, pushRel_of_ne_zero h0, ← foldPush, hfold, List.toFinset_cons]
      exact Finset.ext fun q => by simp [or_left_comm]

-- Decompose the log at its first skipped step.
private theorem traceSteps_split_none :
    ∀ (S₀ : Finset (ι × ℕ)) (w : List ι), none ∈ traceSteps R S₀ w →
      ∃ u b v, w = u ++ b :: v ∧ none ∉ traceSteps R S₀ u ∧
        levelRel R b (foldPush R S₀ u) = 0
  | S₀, [], h => by simp [traceSteps] at h
  | S₀, j :: w, h => by
    by_cases h0 : levelRel R j S₀ = 0
    · exact ⟨[], j, w, rfl, by simp [traceSteps], h0⟩
    simp only [traceSteps, h0, ↓reduceIte, List.mem_cons, reduceCtorEq, false_or] at h
    obtain ⟨u, b, v, rfl, hu, hb⟩ :=
      traceSteps_split_none (insert (j, levelRel R j S₀) S₀) w h
    exact ⟨j :: u, b, v, rfl, by simpa [traceSteps, h0] using hu,
      by simpa only [foldPush, List.foldl_cons, pushRel_of_ne_zero h0] using hb⟩

end Trace

-- Move a skipped step to the front, then drop it.
private theorem erase_first_skipped {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)] (i : ι) (u : List ι) (b : ι)
    (v : List ι)
    (hu : none ∉ traceSteps (lopsidedAdj vbl A) {(i, 0)} u)
    (hb : levelRel (lopsidedAdj vbl A) b (foldPush (lopsidedAdj vbl A) {(i, 0)} u) = 0)
    (hlog : IsLog vbl A T (i :: (u ++ b :: v))) :
    ∃ w', w'.length < (u ++ b :: v).length ∧ IsLog vbl A T (i :: w') ∧
      witnessRel (lopsidedAdj vbl A) i w' = witnessRel (lopsidedAdj vbl A) i (u ++ b :: v) := by
  let R := lopsidedAdj vbl A
  have hRs : ∀ {a b}, R a b → R b a := fun h => (lopsidedAdj_comm vbl A).1 h
  induction u using List.reverseRecOn generalizing v with
  | nil =>
    have hnib : ¬R i b := levelRel_eq_zero hb (mem_singleton_self _)
    have hnlop : ¬Lopsidependent vbl A i b := fun h => hnib (Or.inr h)
    exact ⟨v, by simp, ((isLog_cons vbl).1 (isLog_swap vbl hA hnlop [] v hlog)).2,
      (witnessRel_cons_of_not_rel R hnib v).symm⟩
  | append_singleton u a ih =>
    let S := foldPush R {(i, 0)} u
    have ha : levelRel R a S ≠ 0 := fun h =>
      hu (traceSteps_append R {(i, 0)} u [a] ▸
        List.mem_append_right _ (by simp [traceSteps, h] : none ∈ traceSteps R S [a]))
    have hpush : foldPush R S [a] = insert (a, levelRel R a S) S := pushRel_of_ne_zero ha
    have hb' : levelRel R b (insert (a, levelRel R a S) S) = 0 := by
      rwa [foldPush_append, hpush] at hb
    have hstep : traceSteps R S [a, b] = [some (a, levelRel R a S), none] := by
      simp [traceSteps, ha, hb']
    obtain ⟨hnab, _, hfold⟩ := traceSteps_swap R hRs S hstep (Or.inl rfl)
    have hnlop : ¬Lopsidependent vbl A a b := fun h => hnab (Or.inr h)
    have hswap : IsLog vbl A T (i :: (u ++ b :: a :: v)) :=
      isLog_swap vbl hA hnlop (i :: u) v (by
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using hlog)
    have hu' : none ∉ traceSteps R {(i, 0)} u :=
      fun h => hu (traceSteps_append R {(i, 0)} u [a] ▸ List.mem_append_left _ h)
    rw [levelRel_insert_of_not_rel hnab] at hb'
    obtain ⟨w', hlen, hlog', hw'⟩ := ih (a :: v) hu' hb' hswap
    refine ⟨w', by simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen, hlog', hw'.trans ?_⟩
    simp only [R, S, witnessRel_eq_foldPush, foldPush, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at hfold ⊢
    rw [hfold]

private theorem phase1_elim_none {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)] (i : ι)
    (w : List ι) (hlog : IsLog vbl A T (i :: w)) :
      ∃ w' : List ι, IsLog vbl A T (i :: w') ∧
        witnessRel (lopsidedAdj vbl A) i w' = witnessRel (lopsidedAdj vbl A) i w ∧
        ∃ L : List (ι × ℕ), traceSteps (lopsidedAdj vbl A) {(i, 0)} w' = L.map some := by
  let R := lopsidedAdj vbl A
  by_cases hnone : none ∈ traceSteps R {(i, 0)} w
  · obtain ⟨u, b, v, rfl, hu, hb⟩ := traceSteps_split_none R {(i, 0)} w hnone
    obtain ⟨w', hlen, hlog', hw'⟩ := erase_first_skipped vbl hA i u b v hu hb hlog
    obtain ⟨w'', hlog'', hw'', L, hL⟩ := phase1_elim_none hA i w' hlog'
    exact ⟨w'', hlog'', hw''.trans hw', L, hL⟩
  · match h : (traceSteps R {(i, 0)} w).allSome with
    | none => exact (hnone (List.allSome_eq_none_iff.mp h)).elim
    | some L =>
      refine ⟨w, hlog, rfl, L, ?_⟩
      rw [← List.forall₂_eq_eq_eq, List.forall₂_map_right_iff]
      exact List.allSome_eq_some_iff_forall₂.mp h
termination_by w.length

private theorem phase2_sort_perm {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)] :
    ∀ (c pref : List (ι × ℕ)) (S₀' : Finset (ι × ℕ)) (L : List (ι × ℕ)),
      IsLog vbl A T (pref.map Prod.fst ++ L.map Prod.fst) →
      traceSteps (lopsidedAdj vbl A) S₀' (L.map Prod.fst) = L.map some →
      L.Perm c → c.Pairwise (fun a b => a.2 ≤ b.2) → c.Nodup →
      IsLog vbl A T (pref.map Prod.fst ++ c.map Prod.fst)
  | [], _, _, _, hlog, _, hperm, _, _ => hperm.eq_nil ▸ hlog
  | p :: c', pref, S₀', L, hlog, htr, hperm, hpair, hnod => by
    let R := lopsidedAdj vbl A
    have hRs : ∀ {a b}, R a b → R b a := fun h => (lopsidedAdj_comm vbl A).1 h
    obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem (hperm.symm.subset List.mem_cons_self)
    -- Bring the shallowest step to the front, then sort the rest of the trace.
    suffices hsub : ∀ (front tail : List (ι × ℕ)),
        IsLog vbl A T (pref.map Prod.fst ++ (front ++ p :: tail).map Prod.fst) →
        traceSteps R S₀' ((front ++ p :: tail).map Prod.fst) = (front ++ p :: tail).map some →
        (front ++ p :: tail).Perm (p :: c') →
        IsLog vbl A T (pref.map Prod.fst ++ (p :: c').map Prod.fst) from
      hsub L₁ L₂ hlog htr hperm
    intro front
    induction front using List.reverseRecOn with
    | nil =>
      intro tail hlog' htr' hperm'
      simp only [List.nil_append, List.map_cons, traceSteps] at htr'
      split_ifs at htr'
      · simp at htr'
      · obtain ⟨hp, ht⟩ := List.cons.inj htr'
        rw [Option.some.inj hp] at ht
        have ih := phase2_sort_perm hA c' (pref ++ [p]) (insert p S₀') tail
          (by simpa only [List.map_append, List.map_cons, List.map_nil, List.nil_append,
            List.append_assoc, List.singleton_append] using hlog')
          ht hperm'.cons_inv (List.pairwise_cons.1 hpair).2 (List.nodup_cons.1 hnod).2
        simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.singleton_append] using ih
    | append_singleton front q ih =>
      intro tail hlog' htr' hperm'
      have hperm' : (front ++ q :: p :: tail).Perm (p :: c') := by
        simpa only [List.append_assoc, List.singleton_append] using hperm'
      have hnodL := hperm'.nodup_iff.2 hnod
      have hqp : q ≠ p := fun heq =>
        (List.nodup_cons.1 (List.nodup_append.1 hnodL).2.1).1 (heq ▸ List.mem_cons_self)
      have hqc' : q ∈ c' :=
        (List.mem_cons.1 (hperm'.subset (List.mem_append_right _ List.mem_cons_self))).resolve_left
          hqp
      have hle : p.2 ≤ q.2 := (List.pairwise_cons.1 hpair).1 q hqc'
      let u := front.map Prod.fst
      let v := tail.map Prod.fst
      let S := foldPush R S₀' u
      have happ : traceSteps R S₀' (u ++ ([q.1, p.1] ++ v)) =
          front.map some ++ ([some q, some p] ++ tail.map some) := by
        simpa only [u, v, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          List.nil_append, List.cons_append] using htr'
      rw [traceSteps_append, traceSteps_append] at happ
      obtain ⟨hpre, hrest⟩ := List.append_inj happ (by rw [traceSteps_length]; simp [u])
      obtain ⟨hpairTrace, htail⟩ := List.append_inj hrest (by rw [traceSteps_length]; rfl)
      obtain ⟨hnab, htrace, hfold⟩ := traceSteps_swap R hRs S hpairTrace (Or.inr ⟨p, rfl, hle⟩)
      have hnlop : ¬Lopsidependent vbl A q.1 p.1 := fun h => hnab (Or.inr h)
      apply ih (q :: tail)
      · have hswap := isLog_swap vbl hA hnlop (pref.map Prod.fst ++ u) v (by
          simpa only [u, v, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.nil_append, List.singleton_append] using hlog')
        simpa only [u, v, List.map_append, List.map_cons, List.append_assoc] using hswap
      · simp only [List.map_append, List.map_cons]
        change traceSteps R S₀' (u ++ ([p.1, q.1] ++ v)) = _
        rw [traceSteps_append, traceSteps_append, hpre, htrace, hfold, htail]
        rfl
      · exact (List.Perm.append_left front (List.Perm.swap q p tail)).trans hperm'

/-- Any valid log `i :: w` whose lopsided witness structure is `S` implies that the canonical
depth-ordered log `canonList S` is also valid on `T` [MoserTardos2010, Lemma 6.2]. -/
private theorem isLog_canonList {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)]
    {i : ι} {w : List ι} {S : Finset (ι × ℕ)} (hlog : IsLog vbl A T (i :: w))
    (hS : witnessRel (lopsidedAdj vbl A) i w = S) :
    IsLog vbl A T (canonList S) := by
  let R := lopsidedAdj vbl A
  have hRr : ∀ a, R a a := lopsidedAdj_refl vbl A
  obtain ⟨w₁, hlog₁, hw₁, L, htr⟩ := phase1_elim_none vbl hA i w hlog
  have hS₁ : witnessRel R i w₁ = S := hw₁.trans hS
  obtain ⟨rfl, hnodL, hnotL, hfold⟩ := traceSteps_map_some_eq R hRr {(i, 0)} w₁ L htr
  rw [← witnessRel_eq_foldPush, hS₁] at hfold
  have hnot_root : (i, 0) ∉ L := fun hm => hnotL _ hm (mem_singleton_self _)
  set sorted := S.toList.mergeSort (fun a b => decide (a.2 ≤ b.2))
  have hpermS : sorted.Perm S.toList := List.mergeSort_perm S.toList _
  have hpairS : sorted.Pairwise (fun a b => a.2 ≤ b.2) := by
    simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun a b : ι × ℕ => decide (a.2 ≤ b.2))
      (by grind) (by grind) S.toList
  have hroot : RootedRel R i S := hS₁ ▸ rooted_witnessRel R i (L.map Prod.fst)
  have hmem : (i, 0) ∈ sorted := hpermS.symm.subset (mem_toList.2 hroot.root)
  obtain ⟨p₀, t, hsorted⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  rw [hsorted] at hmem hpairS hpermS
  obtain ⟨hle, hpair_t⟩ := List.pairwise_cons.1 hpairS
  obtain rfl : p₀ = (i, 0) := (List.mem_cons.1 hmem).elim Eq.symm fun hit =>
    hroot.zero p₀ (mem_toList.1 (hpermS.subset List.mem_cons_self))
      (Nat.eq_zero_of_le_zero (hle _ hit))
  have hnod_t : t.Nodup := (List.nodup_cons.1 (hpermS.nodup_iff.2 S.nodup_toList)).2
  have hperm_ins : ((i, 0) :: L).Perm S.toList :=
    (List.perm_ext_iff_of_nodup (List.nodup_cons.2 ⟨hnot_root, hnodL⟩) S.nodup_toList).2
      fun q => by simp [hfold]
  have hperm_t : L.Perm t := (hperm_ins.trans hpermS.symm).cons_inv
  change IsLog vbl A T (sorted.map Prod.fst)
  rw [hsorted, List.map_cons]
  exact phase2_sort_perm vbl hA t [(i, 0)] {(i, 0)} L
    hlog₁ htr hperm_t hpair_t hnod_t

end CanonicalLog

namespace Lopsided

section Measure

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
  (vbl : ι → Finset V)

private def stepCoords (vbl : ι → Finset V) : List ι → Finset (V × ℕ)
  | [] => ∅
  | j :: w => ((vbl j).image fun v => (v, uses vbl w v)) ∪ stepCoords vbl w

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem lt_uses_of_mem_stepCoords :
    ∀ {w : List ι} {p : V × ℕ}, p ∈ stepCoords vbl w → p.2 < uses vbl w p.1
  | [], _, hp => by simp [stepCoords] at hp
  | j :: w, ⟨v, k⟩, hp => by
    simp only [stepCoords, mem_union, mem_image] at hp
    rw [uses_cons]
    rcases hp with ⟨v', hv', he⟩ | hp
    · rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      simp [hv']
    · exact Nat.lt_of_lt_of_le (lt_uses_of_mem_stepCoords hp) (Nat.le_add_right _ _)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem disjoint_stepCoords (j : ι) (w : List ι) :
    Disjoint ((vbl j).image fun v => (v, uses vbl w v)) (stepCoords vbl w) := by
  refine Finset.disjoint_left.2 fun p hp hq => ?_
  obtain ⟨v, -, rfl⟩ := mem_image.1 hp
  exact lt_irrefl _ (lt_uses_of_mem_stepCoords vbl hq)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem isLog_dependsOn (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) :
    ∀ w : List ι, DependsOn (fun T => IsLog vbl A T w) (stepCoords vbl w : Set (V × ℕ))
  | [], T, T', _ => by simp [isLog_nil]
  | j :: w, T, T', h => by
    have hcur : (fun v => T (v, uses vbl w v)) ∈ A j ↔
        (fun v => T' (v, uses vbl w v)) ∈ A j :=
      (hA j fun v hv => h (v, uses vbl w v)
        (Finset.mem_coe.2 (mem_union_left _ (mem_image_of_mem _ (Finset.mem_coe.1 hv))))).to_iff
    have htail : IsLog vbl A T w = IsLog vbl A T' w :=
      isLog_dependsOn A hA w fun c hc =>
        h c (Finset.mem_coe.2 (mem_union_right _ (Finset.mem_coe.1 hc)))
    change IsLog vbl A T (j :: w) = IsLog vbl A T' (j :: w)
    rw [isLog_cons, isLog_cons, funext (current_apply vbl T w), funext (current_apply vbl T' w)]
    exact propext (and_congr hcur (iff_of_eq htail))

/-- For any fixed list `w`, the event `IsLog vbl A T w` reads pairwise disjoint table entries,
so its probability is `∏ j ∈ w, Pr[A j]`. -/
theorem table_isLog_eq_prod (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) :
    ∀ w : List ι, table μ {T | IsLog vbl A T w} = (w.map fun i => Measure.pi μ (A i)).prod
  | [] => by simp [isLog_nil]
  | j :: w => by
    have heq : {T : ∀ p : V × ℕ, α p.1 | IsLog vbl A T (j :: w)} =
        (fun T v => T (v, uses vbl w v)) ⁻¹' A j ∩ {T | IsLog vbl A T w} := by
      ext T
      simp [isLog_cons, funext (current_apply vbl T w)]
    have hd1 : DependsOn
        (· ∈ (fun (T : ∀ p : V × ℕ, α p.1) v => T (v, uses vbl w v)) ⁻¹' A j)
        (((vbl j).image fun v => (v, uses vbl w v)) : Set (V × ℕ)) := fun T T' h =>
      hA j fun v hv => h (v, uses vbl w v)
        (Finset.mem_coe.2 (mem_image_of_mem _ (Finset.mem_coe.1 hv)))
    have hind := indepSet_infinitePi_of_dependsOn (P := fun p : V × ℕ => μ p.1)
      (S := (vbl j).image fun v => (v, uses vbl w v)) (T := stepCoords vbl w)
      (measurable_read (fun v => uses vbl w v) (hAm j)) (measurableSet_isLog vbl A hAm w)
      hd1 (isLog_dependsOn vbl A hA w) (disjoint_stepCoords vbl j w)
    rw [heq, table_def, hind.measure_inter_eq_mul, ← table_def, List.map_cons, List.prod_cons,
      table_isLog_eq_prod A hAm hA w]
    congr 1
    rw [← Measure.map_apply (measurable_read _) (hAm j), table_map_read]

private theorem table_canonList_eq_prod (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (S : Finset (ι × ℕ)) :
    table μ {T | IsLog vbl A T (canonList S)} = ∏ p ∈ S, Measure.pi μ (A p.1) := by
  rw [table_isLog_eq_prod μ vbl A hAm hA (canonList S), canonList, List.map_map,
    ((List.mergeSort_perm S.toList _).map ((fun j => Measure.pi μ (A j)) ∘ Prod.fst)).prod_eq]
  exact Finset.prod_map_toList S _

open scoped Classical in
/-- **Lemma 6.2** of [MoserTardos2010]: the probability that a fixed structure `S` occurs as the
lopsided witness structure of a step of some valid log on the table is at most
`∏ p ∈ S, Pr[A p.1]`. -/
theorem table_witness_le [DecidableEq ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (S : Finset (ι × ℕ)) :
    table μ {T | ∃ i w, IsLog vbl A T (i :: w) ∧
        witnessRel (lopsidedAdj vbl A) i w = S} ≤
      ∏ p ∈ S, Measure.pi μ (A p.1) := by
  refine (measure_mono ?_).trans (table_canonList_eq_prod μ vbl A hAm hA S).le
  exact fun _ ⟨_, _, hlog, hS⟩ => isLog_canonList vbl hA hlog hS

end Measure

section Theorem

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
  (vbl : ι → Finset V)

/-- **Lopsided Moser–Tardos, for all valid logs at once** [MoserTardos2010, Theorem 6.1]. Under
the lopsided local-lemma hypothesis, where `Γ i` contains every other event lopsidependent on
`A i`, the expected supremum over all valid logs of `w.count i` is at most `x i / (1 - x i)`. -/
theorem lintegral_iSup_count_le [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≤
      ENNReal.ofReal (x i / (1 - x i)) := by
  have := Fintype.ofFinite ι
  let _ : DecidableRel (lopsidedAdj vbl A) := Classical.decRel _
  refine lintegral_iSup_count_le_of_pass μ vbl (lopsidedAdj vbl A) (lopsidedAdj_refl vbl A) A
    (fun S T => IsLog vbl A T (canonList S))
    (fun S => measurableSet_isLog vbl A hAm (canonList S))
    (fun S => (table_canonList_eq_prod μ vbl A hAm hA S).le)
    (fun T j H w hw hl => ?_) Γ
    (fun a b hne hadj => hΓ a b hne (hadj.resolve_left hne.symm)) hx hP i
  obtain ⟨W, hcard, hW⟩ := exists_witnessesRel (lopsidedAdj vbl A) (lopsidedAdj_refl vbl A)
    (fun h => (lopsidedAdj_comm vbl A).1 h) j H w hl (IsLog vbl A T)
    (fun a u h => ((isLog_cons vbl).1 h).2) hw
  refine ⟨W, hcard, fun S hS => ?_⟩
  obtain ⟨hsh, -, u, hu, hiu⟩ := hW S hS
  exact ⟨hsh, isLog_canonList vbl hA hiu hu.symm⟩

/-- **Lopsided Moser–Tardos theorem** [MoserTardos2010, Theorem 6.1]. Let `x i ∈ [0, 1)` with
`Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)`, where `Γ i` contains every other event lopsidependent on
`A i`. Then every valid selection rule resamples `A i` at most `x i / (1 - x i)` times in
expectation. -/
theorem lintegral_resamplings_le [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) :=
  lintegral_resamplings_le_of_bound μ vbl A (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)
    hsel

/-- **Theorem 6.1 for the outer expectation** [MoserTardos2010]: one measurable function with
expectation at most `x i / (1 - x i)` bounds the resampling count under every valid rule. -/
theorem exists_measurable_ge_resamplings [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) ∧
      ∀ sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι,
        (∀ T w j, sel T w = some j → current vbl T w ∈ A j) →
          ∀ T, resamplings sel i T ≤ g T :=
  exists_measurable_ge_resamplings_of_bound μ vbl A hAm
    (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)

/-- **Expected total resamplings under lopsidependence** [MoserTardos2010, Theorem 6.1]: at most
`∑ i, x i / (1 - x i)` for every valid selection rule. -/
theorem lintegral_sum_resamplings_le [DecidableEq ι] [Fintype ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ ∑ i, ENNReal.ofReal (x i / (1 - x i)) :=
  lintegral_sum_resamplings_le_of_bound μ vbl A hAm
    (fun i => lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i) hsel

/-- **Termination under lopsidependence** [MoserTardos2010, Theorem 6.1]: almost surely every
valid rule stops in finitely many steps. -/
theorem ae_exists_run_eq_none [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∀ᵐ T ∂table μ, ∃ n, sel T (run sel T n) = none :=
  ae_exists_run_eq_none_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))
    hsel

/-- **Algorithmic lopsided local lemma** [MoserTardos2010, Theorem 6.1]: almost surely any valid
rule that stops only when no event occurs reaches an avoiding assignment. -/
theorem ae_exists_forall_notMem_run [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i :=
  ae_exists_forall_notMem_run_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))
    hsel hstop

/-- **Greedy lopsided Moser–Tardos** [MoserTardos2010, Theorem 6.1]: almost surely the greedy run
reaches an assignment avoiding every event. -/
theorem ae_exists_forall_notMem_run_greedy [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run (greedy vbl A) T n) ∉ A i :=
  ae_exists_forall_notMem_run_greedy_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))

/-- **Constructive lopsided local lemma** [MoserTardos2010, Theorem 6.1]. -/
theorem exists_forall_notMem [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  exact exists_forall_notMem_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))

section Symmetric

/-- **Symmetric lopsided Moser–Tardos** (`1 ≤ d`): expected resamplings at most `1 / d` when each
`A i` has probability at most `q`, lopsidependency degree at most `d`, and `e * q * (d + 1) ≤ 1`. -/
theorem lintegral_resamplings_le_symmetric [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hdpos : 1 ≤ d) (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (1 / (d : ℝ)) := by
  obtain ⟨x, hx, hP, hx1, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact (lintegral_resamplings_le μ vbl A hAm hA Γ hΓ hx hP hsel i).trans
    (le_of_eq (congrArg ENNReal.ofReal (hx1 hdpos i)))

/-- Expected total resamplings under symmetric lopsided Moser–Tardos (`1 ≤ d`). -/
theorem lintegral_sum_resamplings_le_symmetric [DecidableEq ι] [Fintype ι]
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hdpos : 1 ≤ d) (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ Fintype.card ι * ENNReal.ofReal (1 / (d : ℝ)) := by
  obtain ⟨x, hx, hP, hx1, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  have h := lintegral_sum_resamplings_le μ vbl A hAm hA Γ hΓ hx hP hsel
  simpa only [hx1 hdpos, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- Almost sure success under symmetric lopsided Moser–Tardos (`e * q * (d + 1) ≤ 1`) for every
`d : ℕ`. -/
theorem ae_exists_forall_notMem_run_symmetric [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i := by
  obtain ⟨x, hx, hP, -, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact ae_exists_forall_notMem_run μ vbl A hAm hA Γ hΓ hx hP hsel hstop

/-- **Symmetric constructive lopsided local lemma** (`e * q * (d + 1) ≤ 1`). -/
theorem exists_forall_notMem_symmetric [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  obtain ⟨x, hx, hP, -, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact exists_forall_notMem μ vbl A hAm hA Γ hΓ hx hP

end Symmetric

end Theorem

end Lopsided

end Cslib.Probability.MoserTardos
