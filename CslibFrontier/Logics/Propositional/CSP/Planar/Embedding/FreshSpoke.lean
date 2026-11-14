/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Attachment
import Mathlib.Tactic.FinCases

/-!
# Literal fresh spokes on an ordered body

A binary atom joins a selected boundary marker to a fresh name. Deleting the old marker
replaces it in situ. Freshness is required only on the actual body and boundary support.
This supplies the exact row order used by normalization's one- and two-edge spokes.

## Main definitions

* `Witness.namedAtom`: the ordered atom witness under injective actual labels.
* `Witness.freshSpoke`: append one literal binary row and replace its selected marker.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V : Type} [DecidableEq V]

/-- An injectively named literal has its ordered numerical witness by renaming the
public arbitrary-arity atom witness. No semantics or geometric provider is needed. -/
def Witness.namedAtom (r : Rel) {n : ℕ} (v : Fin n → V) (hv : Function.Injective v) :
    Witness [⟨r, List.ofFn v⟩] (List.ofFn v) := by
  let f : Fin n ⊕ Fin 0 → V := Sum.elim v Fin.elim0
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (hv h)
      | inr b => exact b.elim0
    | inr a => exact a.elim0
  let h := (Witness.atom (fun _ : Rel => n) (fun _ _ => false) r).relabel f
    (fun _ _ _ _ he => hf he)
  exact ⟨h.certificate, by
    simpa only [PPGadget.atom, CSP.relabel, Constraint.relabel, List.map_cons, List.map_nil,
      List.map_ofFn, Function.comp_def, f, Sum.elim_inl] using h.accepted⟩

private theorem freshSpoke_kernel {F : CSP Rel V} {left right : List V} {x z : V}
    (hz : z ∉ F.vars ++ (left ++ x :: right))
    (a b : V ⊕ Fin 2)
    (ha : a ∈ (F.vars ++ (left ++ x :: right)).map Sum.inl ++
      [Sum.inr 0, Sum.inr 1])
    (hb : b ∈ (F.vars ++ (left ++ x :: right)).map Sum.inl ++
      [Sum.inr 0, Sum.inr 1]) :
    Sum.elim id ((fun i : Fin 2 => if i = 0 then x else z)) a =
      Sum.elim id ((fun i : Fin 2 => if i = 0 then x else z)) b ↔
        Function.update id (Sum.inl x) (Sum.inr 0) a =
          Function.update id (Sum.inl x) (Sum.inr 0) b := by
  have hxz : x ≠ z := by
    intro he
    exact hz (by simp [← he])
  have hfresh (c : V) (hc : (Sum.inl c : V ⊕ Fin 2) ∈
      (F.vars ++ (left ++ x :: right)).map Sum.inl ++ [Sum.inr 0, Sum.inr 1]) : c ≠ z := by
    intro he
    subst c
    exact hz (by simpa using hc)
  cases a with
  | inl a =>
    have haz := hfresh a ha
    cases b with
    | inl b =>
      by_cases hax : a = x <;> by_cases hbx : b = x <;>
        simp_all [eq_comm]
    | inr b =>
      fin_cases b <;> by_cases hax : a = x <;> simp_all [eq_comm]
  | inr a =>
    cases b with
    | inl b =>
      have hbz := hfresh b hb
      fin_cases a <;> by_cases hbx : b = x <;> simp_all [eq_comm]
    | inr b => fin_cases a <;> fin_cases b <;> simp [hxz, eq_comm]

/-- Append exactly the row `r(x,z)` and replace boundary marker `x` by fresh marker `z`.
All other body rows, scope entries and boundary positions retain their literal order. -/
noncomputable def Witness.freshSpoke {F : CSP Rel V} {left right : List V} {x z : V}
    (w : Witness F (left ++ x :: right)) (r : Rel)
    (hn : (left ++ x :: right).Nodup) (hz : z ∉ F.vars ++ (left ++ x :: right)) :
    Witness (F ++ [⟨r, [x, z]⟩]) (left ++ z :: right) := by
  let H : CSP Rel (Fin 2) := [⟨r, [0, 1]⟩]
  have hH : H.vars = [0, 1] := rfl
  let v : Witness H ([1] ++ [0]) :=
    (Witness.namedAtom r (id : Fin 2 → Fin 2) Function.injective_id).rotateCons (by decide)
  let wtag := w.relabel (Sum.inl : V → V ⊕ Fin 2) (fun _ _ _ _ h => Sum.inl.inj h)
  let vtag := v.relabel (Sum.inr : Fin 2 → V ⊕ Fin 2) (fun _ _ _ _ h => Sum.inr.inj h)
  let f : V ⊕ Fin 2 → V := Sum.elim id ((fun i : Fin 2 => if i = 0 then x else z))
  have hnew : (left ++ z :: x :: right).Nodup := by
    have hzl : z ∉ left ++ x :: right := by
      intro h
      exact hz (List.mem_append_right _ h)
    have h := (List.nodup_cons.mpr ⟨hzl, hn⟩).perm
      (List.perm_middle (a := z) (l₁ := left) (l₂ := x :: right)).symm
    exact h
  let wt : Witness (F.relabel (Sum.inl : V → V ⊕ Fin 2))
      (left.map Sum.inl ++ Sum.inl x :: right.map Sum.inl) :=
    ⟨wtag.certificate, by simpa only [List.map_append, List.map_cons] using wtag.accepted⟩
  let vt : Witness (H.relabel (Sum.inr : Fin 2 → V ⊕ Fin 2))
      ([Sum.inr 1] ++ [Sum.inr 0]) := ⟨vtag.certificate, vtag.accepted⟩
  let h := wt.attachAt vt f
    (by
      apply List.disjoint_left.mpr
      intro a ha hb
      simp only [CSP.vars_relabel, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at ha hb
      rcases ha with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ | rfl | ⟨a, _, rfl⟩ <;>
        simp [H, CSP.vars] at hb)
    (by
      simpa only [List.map_append, List.map_cons] using
        List.nodup_append.mpr ⟨hn.map Sum.inl_injective, by simp,
          by simp⟩)
    (by
      intro a ha b hb
      apply freshSpoke_kernel hz a b
      · simpa only [CSP.vars_relabel, List.map_append, List.map_cons, List.map_nil,
          hH, List.append_nil,
          List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false, false_or,
          or_assoc, or_comm, or_left_comm, or_self] using ha
      · simpa only [CSP.vars_relabel, List.map_append, List.map_cons, List.map_nil,
          hH, List.append_nil,
          List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false, false_or,
          or_assoc, or_comm, or_left_comm, or_self] using hb)
    (by simpa [f] using hnew)
  have hbody : ((F.relabel (Sum.inl : V → V ⊕ Fin 2) ++ H.relabel Sum.inr).relabel f) =
      F ++ [⟨r, [x, z]⟩] := by
    simp [CSP.relabel, Constraint.relabel, List.map_append, List.map_map,
      Function.comp_def, f, H]
  let h' : Witness (F ++ [⟨r, [x, z]⟩]) (left ++ z :: x :: right) :=
    ⟨h.certificate, by
      simpa [hbody, f, List.map_map, Function.comp_def, List.append_assoc] using h.accepted⟩
  let out := h'.forgetAt (left.length + 1) hnew (by simp)
  exact ⟨out.certificate, by
    have hdel : (left ++ z :: x :: right).eraseIdx (left.length + 1) = left ++ z :: right := by
      rw [List.eraseIdx_append_of_length_le (by omega)]
      simp
    rw [← hdel]
    exact out.accepted⟩

end Cslib.Complexity.CSP.OrderedBoundary
