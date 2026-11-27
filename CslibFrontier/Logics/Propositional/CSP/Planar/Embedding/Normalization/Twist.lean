/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Normalization
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.FreshSpoke
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic

/-!
# The literal normalization twist

Start with the original relation atom on the inner labels and append the specified one- or
two-edge disequality spokes in increasing port order. Each attachment replaces its boundary
marker in place. The body and the entire `2n` auxiliary label type are exactly those of
`Normalization.twistBody`, including unused middle labels on flipped spokes.

This is an original numerical witness construction for the combinatorial reconstruction of
[DvorakKupec2015], §4, printed p. 440, Lemma 6 (whose proof is omitted there). It asserts no
equivalence with the source's geometric plane-instance model and no preprocessing-time bound.
-/

public section

namespace Cslib.Logic.PL.CSP.Normalization

open Cslib.Complexity.CSP.OrderedBoundary

private noncomputable def freshSpokeOfFn {V : Type} [DecidableEq V]
    {F : CSP Symbol V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hv : Function.Injective v) (j : Fin n) (z : V)
    (hz : z ∉ F.vars ++ List.ofFn v) :
    Witness (F ++ [⟨.disequality, [v j, z]⟩]) (List.ofFn (Function.update v j z)) := by
  let ports := List.ofFn v
  let left := ports.take j.val
  let right := ports.drop (j.val + 1)
  have hj : j.val < ports.length := by simpa only [ports, List.length_ofFn] using j.isLt
  have hword : left ++ v j :: right = ports := by
    change ports.take j.val ++ v j :: ports.drop (j.val + 1) = ports
    have he : ports[j.val] = v j := by simp only [ports, List.getElem_ofFn]
    rw [← he, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let w' : Witness F (left ++ v j :: right) :=
    ⟨w.certificate, by rw [hword]; exact w.accepted⟩
  let h := w'.freshSpoke .disequality (by rw [hword]; exact List.nodup_ofFn.mpr hv)
    (by rw [hword]; exact hz)
  have hout : List.ofFn (Function.update v j z) = left ++ z :: right := by
    rw [← List.set_ofFn, List.set_eq_take_append_cons_drop]
    exact ite_eq_left hj
  exact ⟨h.certificate, by rw [hout]; exact h.accepted⟩

private def spoke {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    CSP Symbol (Fin n ⊕ Fin (n + n)) :=
  if a i then [⟨.disequality, [.inr (i.castAdd n), .inl i]⟩]
  else [⟨.disequality, [.inr (i.castAdd n), .inr (i.natAdd n)]⟩,
    ⟨.disequality, [.inr (i.natAdd n), .inl i]⟩]

private def partialBody {n : ℕ} (a : Fin n → Bool) (k : ℕ) :
    CSP Symbol (Fin n ⊕ Fin (n + n)) :=
  ⟨.relation, List.ofFn (fun i : Fin n => Sum.inr (i.castAdd n))⟩ ::
    ((List.finRange n).take k).flatMap (spoke a)

private def frontier (n k : ℕ) (i : Fin n) : Fin n ⊕ Fin (n + n) :=
  if i.val < k then .inl i else .inr (i.castAdd n)

private theorem frontier_injective (n k : ℕ) : Function.Injective (frontier n k) := by
  intro i j h
  unfold frontier at h
  split_ifs at h <;> simp_all

private theorem partialBody_support {n : ℕ} (a : Fin n → Bool) (k : ℕ)
    (z : Fin n ⊕ Fin (n + n)) (hz : z ∈ (partialBody a k).vars) :
    (∃ i : Fin n, z = .inr (i.castAdd n)) ∨
      ∃ i : Fin n, i.val < k ∧ (z = .inl i ∨ z = .inr (i.natAdd n)) := by
  simp only [partialBody, CSP.vars, List.flatMap_cons, List.mem_append, List.mem_ofFn,
    List.mem_flatMap] at hz
  rcases hz with ⟨i, rfl⟩ | ⟨c, ⟨i, hi, hc⟩, hz⟩
  · exact Or.inl ⟨i, rfl⟩
  · have hik : i.val < k := by
      obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hi
      have he' := congrArg Fin.val he
      simp only [List.getElem_finRange, Fin.val_cast] at he'
      omega
    unfold spoke at hc
    split_ifs at hc
    · simp only [List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i, hik, Or.inl rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      · rcases hz with rfl | rfl
        · exact Or.inl ⟨i, rfl⟩
        · exact Or.inr ⟨i, hik, Or.inr rfl⟩
      · rcases hz with rfl | rfl
        · exact Or.inr ⟨i, hik, Or.inr rfl⟩
        · exact Or.inr ⟨i, hik, Or.inl rfl⟩

private theorem freshLabels {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    Sum.inl i ∉ (partialBody a i.val).vars ++ List.ofFn (frontier n i.val) ∧
      Sum.inr (i.natAdd n) ∉ (partialBody a i.val).vars ++ List.ofFn (frontier n i.val) := by
  constructor <;> intro h <;> rcases List.mem_append.mp h with h | h
  · rcases partialBody_support a i.val _ h with ⟨j, he⟩ | ⟨j, hj, he | he⟩ <;>
      simp_all [Fin.ext_iff]; omega
  · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    unfold frontier at hj
    split_ifs at hj; simp_all [Fin.ext_iff]; omega
  · rcases partialBody_support a i.val _ h with ⟨j, he⟩ | ⟨j, hj, he | he⟩ <;>
      simp_all [Fin.ext_iff] <;> omega
  · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
    unfold frontier at hj
    split_ifs at hj; simp_all [Fin.ext_iff]; omega

private theorem partialBody_succ {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    partialBody a (i.val + 1) = partialBody a i.val ++ spoke a i := by
  unfold partialBody
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using i.isLt)]
  simp [List.flatMap_append]

private theorem frontier_update {n : ℕ} (i : Fin n) :
    Function.update (frontier n i.val) i (Sum.inl i) = frontier n (i.val + 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [frontier]
  · have hv : j.val ≠ i.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, frontier]
    have hiff : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp only [hiff]

private noncomputable def partialWitness {n : ℕ} (a : Fin n → Bool) (k : ℕ) (hk : k ≤ n) :
    Witness (partialBody a k) (List.ofFn (frontier n k)) := by
  induction k with
  | zero =>
    have hp : frontier n 0 = fun i : Fin n => (Sum.inr (i.castAdd n) : Fin n ⊕ Fin (n + n)) := by
      funext i
      simp [frontier]
    rw [hp]
    simpa only [partialBody, List.take_zero, List.flatMap_nil] using
      Witness.namedAtom (Rel := Symbol) .relation
        (fun i : Fin n => (Sum.inr (i.castAdd n) : Fin n ⊕ Fin (n + n)))
        (by intro i j he; exact Fin.castAdd_injective n n (Sum.inr.inj he))
  | succ k ih =>
    let i : Fin n := ⟨k, by omega⟩
    let w : Witness (partialBody a k) (List.ofFn (frontier n k)) := ih (by omega)
    have hinner : frontier n k i = .inr (i.castAdd n) := by simp [frontier, i]
    have hfresh := freshLabels a i
    by_cases ha : a i = true
    · let h := freshSpokeOfFn w (frontier_injective n k) i (Sum.inl i) hfresh.1
      have hb : partialBody a (k + 1) = partialBody a k ++
          [⟨.disequality, [frontier n k i, Sum.inl i]⟩] := by
        rw [partialBody_succ a i]
        simp only [spoke, ha, ite_true, hinner]
        rfl
      have hp : Function.update (frontier n k) i (Sum.inl i) = frontier n (k + 1) :=
        frontier_update i
      rw [hb, ← hp]
      exact h
    · let h := freshSpokeOfFn w (frontier_injective n k) i (Sum.inr (i.natAdd n)) hfresh.2
      have hv : Function.Injective (Function.update (frontier n k) i
          (Sum.inr (i.natAdd n))) := by
        intro j l he
        by_cases hj : j = i
        · subst j
          by_cases hl : l = i
          · exact hl.symm
          · rw [Function.update_self, Function.update_of_ne hl] at he
            exact False.elim (hfresh.2 (List.mem_append_right _
              (List.mem_ofFn.mpr ⟨l, he.symm⟩)))
        · by_cases hl : l = i
          · subst l
            rw [Function.update_self, Function.update_of_ne hj] at he
            exact False.elim (hfresh.2 (List.mem_append_right _
              (List.mem_ofFn.mpr ⟨j, he⟩)))
          · rw [Function.update_of_ne hj, Function.update_of_ne hl] at he
            exact frontier_injective n k he
      have hz : Sum.inl i ∉ ((partialBody a k ++
          [⟨.disequality, [frontier n k i, Sum.inr (i.natAdd n)]⟩]) :
            CSP Symbol (Fin n ⊕ Fin (n + n))).vars ++
            List.ofFn (Function.update (frontier n k) i (Sum.inr (i.natAdd n))) := by
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · have hm' : Sum.inl i ∈ (partialBody a k).vars ∨
              Sum.inl i = frontier n k i ∨ Sum.inl i = Sum.inr (i.natAdd n) := by
            simpa only [CSP.vars, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using hm
          rcases hm' with hm | he | he
          · exact hfresh.1 (List.mem_append_left _ hm)
          · simp [hinner] at he
          · cases he
        · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
          by_cases hji : j = i
          · subst j; simp at hj
          · exact hfresh.1 (List.mem_append_right _ (List.mem_ofFn.mpr
              ⟨j, by simpa only [Function.update_of_ne hji] using hj⟩))
      let out := freshSpokeOfFn h hv i (Sum.inl i) hz
      have hup : Function.update (Function.update (frontier n k) i
          (Sum.inr (i.natAdd n))) i (Sum.inl i) = frontier n (k + 1) := by
        rw [Function.update_idem]
        exact frontier_update i
      have hb : partialBody a (k + 1) = (partialBody a k ++
          [⟨.disequality, [frontier n k i, Sum.inr (i.natAdd n)]⟩]) ++
            [⟨.disequality, [Sum.inr (i.natAdd n), Sum.inl i]⟩] := by
        rw [partialBody_succ a i]
        simp only [spoke, ha, hinner, List.append_assoc, List.singleton_append]
        rfl
      rw [hb, ← hup]
      simpa only [Function.update_self] using out

/-- The exact twist body, with all original and redundant auxiliary labels, has an
internally constructed ordered numerical witness at every arity, including zero. This is
also definitionally a `GadgetWitness (twistGadget R a)` for any relation `R`. -/
noncomputable def twistBodyWitness {n : ℕ} (a : Fin n → Bool) :
    Witness (twistBody a) (List.ofFn Sum.inl) := by
  let h := partialWitness a n le_rfl
  have htake : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  have hp : frontier n n = Sum.inl := by
    funext i
    simp [frontier]
  have hb : partialBody a n = twistBody a := by
    simp only [partialBody, htake]
    rfl
  rw [← hb, ← hp]
  exact h

end Cslib.Logic.PL.CSP.Normalization
