/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryFusion
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryHiding
import Mathlib.Logic.Function.Basic

/-!
# Closing the first actual metadata run

`closeFirstMetadataRun` executes one head fusion per remaining member of the actual first
run, then hides its survivor once. Mismatch and empty input retain the entire raw State.
The collapse theorem tracks global renaming, including repeated names outside the selected
positions. Recovery uses that collapse; forwarding a group-consistent assignment preserves
EVERY old name. This original operation is a step toward the full compiler of
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091), not the all-runs driver.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Rel : Type}

/-- Close only the first consecutive equal-key run. The ACTUAL run tail funds the private
fold; binary key magnitudes never count iterations. The certificate is the literal sequence
of existing fusions and one final hide, with no chosen replacement table. -/
@[expose] def closeFirstMetadataRun (I : State Rel) (keys : List ℕ) : State Rel :=
  if keys.length ≠ I.ports.length then I else
    match keys with
    | [] => I
    | a :: ks =>
      let run := (a :: ks).takeWhile (fun b => decide (b=a))
      hideHead (run.tail.foldl (fun J _ => fuseHead J) I)

private def collapseTo (x : ℕ) (xs : List ℕ) (z : ℕ) : ℕ :=
  if z ∈ xs then x else z

private theorem collapse_step (x y : ℕ) (ys : List ℕ) :
    collapseTo x (ys.map (Function.update id y x)) ∘ Function.update id y x =
      collapseTo x (y::ys) := by
  funext z
  let f := Function.update id y x
  by_cases hzy : z = y
  · subst z
    simp [collapseTo]
  · by_cases hzs : z ∈ ys
    · have hm : f z ∈ ys.map f := List.mem_map.mpr ⟨z,hzs,rfl⟩
      change (if f z ∈ ys.map f then x else f z) = collapseTo x (y :: ys) z
      rw [ite_eq_left hm]
      simp [collapseTo, hzs]
    · have hfix : collapseTo x (ys.map f) z = z := by
        by_cases hm : z ∈ ys.map f
        · obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
          by_cases hvy : v = y
          · subst v
            have hx : x = z := by simpa only [f, Function.update_self] using he
            simp [collapseTo,hm,hx]
          · have hvz : v = z := by simpa only [f, Function.update_of_ne hvy, id_eq] using he
            exact (hzs (hvz ▸ hv)).elim
        · simp only [collapseTo, ite_eq_right hm]
      simpa only [Function.comp_apply, f, Function.update_of_ne hzy, id_eq,
        collapseTo, List.mem_cons, hzy, false_or, ite_eq_right hzs] using hfix

private theorem fusion_fields (tasks : List ℕ) (F : CSP Rel ℕ) (x : ℕ)
    (xs rest : List ℕ) (c : RotationCertificate) (hlen : tasks.length = xs.length) :
    let J := tasks.foldl (fun J _ => fuseHead J) (⟨F,x::(xs++rest),c⟩ : State Rel)
    J.body = F.relabel (collapseTo x xs) ∧
      J.ports = x::rest.map (collapseTo x xs) := by
  induction tasks generalizing F xs rest c with
  | nil =>
    have hx : xs = [] := by simpa only [List.length_nil, List.length_eq_zero_iff] using hlen.symm
    subst xs
    change F = F.relabel (collapseTo x []) ∧ x :: rest = x :: rest.map (collapseTo x [])
    have hz : collapseTo x [] = id := by funext z; simp [collapseTo]
    rw [hz]
    constructor
    · rw [CSP.relabel]
      calc
        F = F.map id := (List.map_id F).symm
        _ = F.map (Constraint.relabel id) := by
          apply List.map_congr_left
          intro c _
          cases c
          simp [Constraint.relabel]
    · simp
  | cons t ts ih =>
    cases xs with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons y ys =>
      let f := Function.update id y x
      let d := equalDropCertificate F (ys++rest).length c
      have ht : ts.length = (ys.map f).length := by simp only [List.length_map]; simpa using hlen
      have h := ih (F.relabel f) (ys.map f) (rest.map f) d ht
      have hj : fuseHead (⟨F,x::((y::ys)++rest),c⟩ : State Rel) =
          ⟨F.relabel f,x::(ys.map f++rest.map f),d⟩ := by
        simp [f,d,fuseHead]
      simp only [List.foldl_cons,hj]
      refine ⟨h.1.trans ?_, h.2.trans ?_⟩
      · have hc := congrArg (fun k => F.relabel k) (collapse_step x y ys)
        calc
          (F.relabel f).relabel (collapseTo x (ys.map f)) =
              F.relabel (collapseTo x (ys.map f) ∘ f) := by
            simp only [CSP.relabel, List.map_map]
            congr 1
            funext c
            cases c
            simp [Constraint.relabel, Function.comp_def, List.map_map]
          _ = _ := hc
      · rw [List.map_map]
        exact congrArg (fun k => x::rest.map k) (collapse_step x y ys)

/-- The executed fold globally collapses the selected names, removes exactly that prefix,
and emits the literal final restriction with its unconditional raw entry bound. This needs
only actual list alignment, not acceptance, arity or distinct names. -/
theorem fields_closeFirstMetadataRun (I : State Rel) (a : ℕ) (ks : List ℕ)
    (hl : (a::ks).length = I.ports.length) :
    let r := ((a::ks).takeWhile (fun b => decide (b = a))).length
    let C := fun z => if z ∈ I.ports.take r then I.ports.headD 0 else z
    let K := closeFirstMetadataRun I (a::ks)
    K.body = I.body.relabel C ∧ K.ports = (I.ports.drop r).map C ∧
      K.rotation.successor.length = 2*(I.body.occurrences.length+I.ports.length-r) ∧
      ∀ v ∈ K.rotation.successor, v < 2*(I.body.occurrences.length+I.ports.length-r) := by
  rcases I with ⟨F,ports,c⟩
  cases ports with
  | nil => simp only [List.length_cons,List.length_nil] at hl; omega
  | cons x ps =>
    let R := ks.takeWhile (fun b => decide (b = a))
    have hR : R.length ≤ ps.length := by
      have ht := (List.takeWhile_sublist (fun b => decide (b = a)) (l := ks)).length_le
      simp only [List.length_cons] at hl
      dsimp only [R]
      omega
    let pre := ps.take R.length
    let rest := ps.drop R.length
    let J := R.foldl (fun J _ => fuseHead J) (⟨F,x::ps,c⟩ : State Rel)
    have hp : pre++rest = ps := List.take_append_drop _ _
    have hf := fusion_fields R F x pre rest c (by simp [pre,Nat.min_eq_left hR])
    rw [hp] at hf
    change J.body = F.relabel (collapseTo x pre) ∧ J.ports = x::rest.map (collapseTo x pre) at hf
    have hm : J.body.occurrences.length = F.occurrences.length := by
      rw [← CSP.vars_length_eq_occurrences, hf.1, CSP.vars_relabel,
        List.length_map, CSP.vars_length_eq_occurrences]
    have hC : (fun z => if z ∈ (x::ps).take (R.length+1) then (x::ps).headD 0 else z) =
        collapseTo x pre := by
      funext z
      by_cases hz : z = x <;> simp [collapseTo,pre,hz,List.take_succ_cons]
    have hK : closeFirstMetadataRun (⟨F,x::ps,c⟩ : State Rel) (a::ks) = hideHead J := by
      simp [closeFirstMetadataRun,hl,J,R]
    dsimp only
    simp only [List.takeWhile_cons, decide_true, ↓reduceIte,
      List.length_cons]
    rw [show (ks.takeWhile (fun b => decide (b = a))).length+1 = R.length+1 from rfl,hC,hK]
    have hd : (hideHead J).rotation =
        restrictPrefix (2*(F.occurrences.length+rest.length)) J.rotation := by
      simp only [hideHead,hf.2,hm,List.length_map]
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [hideHead,hf.2] using hf.1
    · simp only [hideHead,hf.2]
      simp only [rest,List.drop_succ_cons]
    · rw [hd,length_restrictPrefix]
      simp only [rest,List.length_drop]
      omega
    · rw [hd]
      have he := entries_restrictPrefix_lt (2*(F.occurrences.length+rest.length)) J.rotation
      intro v hv
      have hv' := he v hv
      simp only [rest, List.length_drop] at hv' ⊢
      omega

/-- Mismatch and empty metadata retain every raw field, without normalization. -/
theorem closeFirstMetadataRun_eq_self (I : State Rel) (keys : List ℕ)
    (h : keys.length ≠ I.ports.length ∨ keys = []) : closeFirstMetadataRun I keys = I := by
  rcases h with h | rfl
  · simp only [closeFirstMetadataRun,ite_eq_left h]
  · simp [closeFirstMetadataRun]

private theorem accepted_fusion_fold (tasks : List ℕ) (I : State Rel) (hI : I.Accepted) :
    (tasks.foldl (fun J _ => fuseHead J) I).Accepted := by
  induction tasks generalizing I with
  | nil => exact hI
  | cons t ts ih => exact ih (fuseHead I) (accepted_fuseHead I hI)

/-- Each executed fusion and the single hide internally preserve the full checker. -/
theorem accepted_closeFirstMetadataRun (I : State Rel) (keys : List ℕ) (hI : I.Accepted) :
    (closeFirstMetadataRun I keys).Accepted := by
  unfold closeFirstMetadataRun
  split
  · exact hI
  · cases keys with
    | nil => exact hI
    | cons a ks =>
      apply accepted_hideHead
      exact accepted_fusion_fold _ I hI

/-- Rows, every indexed relation/scope-width pair, occurrences and residual port count are
preserved exactly as the raw first-run program specifies. No semantic guard is used. -/
theorem components_closeFirstMetadataRun (I : State Rel) (keys : List ℕ) :
    let r := if keys.length = I.ports.length then
      (keys.takeWhile (fun b => decide (b = keys.headD 0))).length else 0
    let K := closeFirstMetadataRun I keys
    K.body.length = I.body.length ∧ K.body.occurrences.length = I.body.occurrences.length ∧
      K.body.map (fun c => (c.rel,c.scope.length))=
        I.body.map (fun c => (c.rel,c.scope.length)) ∧ K.ports.length = I.ports.length-r := by
  dsimp only
  by_cases hl : keys.length = I.ports.length
  · cases keys with
    | nil => simp [closeFirstMetadataRun]
    | cons a ks =>
      have hf := fields_closeFirstMetadataRun I a ks hl
      dsimp only at hf
      rw [hf.1,hf.2.1]
      simp [hl,CSP.relabel,Constraint.relabel,CSP.length_occurrences,List.map_map,Function.comp_def]
  · rw [closeFirstMetadataRun_eq_self I keys (Or.inl hl)]
    simp only [hl,↓reduceIte,Nat.sub_zero,and_self]

/-- Exact arity iff on EVERY raw input, including mismatch, repeated names and nullaries. -/
theorem wellFormed_closeFirstMetadataRun_iff (ar : Rel → ℕ) (I : State Rel) (keys : List ℕ) :
    (closeFirstMetadataRun I keys).body.WellFormed ar ↔ I.body.WellFormed ar := by
  by_cases hl : keys.length = I.ports.length
  · cases keys with
    | nil => simp [closeFirstMetadataRun]
    | cons a ks =>
      rw [(fields_closeFirstMetadataRun I a ks hl).1]
      simp [CSP.WellFormed,CSP.relabel,Constraint.relabel]
  · rw [closeFirstMetadataRun_eq_self I keys (Or.inl hl)]

/-- No new variable name is invented: every raw output name is selected from the original
body or boundary, including names that were repeated outside the selected positions. -/
theorem names_closeFirstMetadataRun_subset (I : State Rel) (keys : List ℕ) :
    (closeFirstMetadataRun I keys).body.vars ++ (closeFirstMetadataRun I keys).ports ⊆
      I.body.vars ++ I.ports := by
  by_cases hl : keys.length = I.ports.length
  · cases keys with
    | nil => simp [closeFirstMetadataRun]
    | cons a ks =>
      have hf := fields_closeFirstMetadataRun I a ks hl
      dsimp only at hf
      rw [hf.1,hf.2.1,CSP.vars_relabel,← List.map_append]
      intro z hz
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
      split
      · apply List.mem_append_right
        cases hp : I.ports with
        | nil => simp only [hp,List.length_nil,List.length_cons] at hl; omega
        | cons x ps => simp
      · rcases List.mem_append.mp hv with hv | hv
        · exact List.mem_append_left _ hv
        · exact List.mem_append_right _ ((List.drop_sublist _ _).subset hv)
  · rw [closeFirstMetadataRun_eq_self I keys (Or.inl hl)]

/-- ONE output assignment pulls back through the actual global collapse and determines
both source truth and the exact residual ordered word. All selected source values agree. -/
theorem recover_closeFirstMetadataRun (sem : Rel → List Bool → Bool) (I : State Rel)
    (a : ℕ) (ks : List ℕ) (hl : (a::ks).length = I.ports.length) (τ : ℕ → Bool)
    (ht : (closeFirstMetadataRun I (a::ks)).body.eval sem τ = true) :
    let r := ((a::ks).takeWhile (fun b => decide (b = a))).length
    let C := fun z => if z ∈ I.ports.take r then I.ports.headD 0 else z
    I.body.eval sem (τ ∘ C) = true ∧
      (∀ z ∈ I.ports.take r, τ (C z) = τ (I.ports.headD 0)) ∧
      (closeFirstMetadataRun I (a::ks)).ports.map τ = (I.ports.drop r).map (τ ∘ C) := by
  have hf := fields_closeFirstMetadataRun I a ks hl
  dsimp only at hf ⊢
  rw [hf.1,CSP.eval_relabel] at ht
  refine ⟨ht,?_,?_⟩
  · intro z hz
    rw [ite_eq_left hz]
  · rw [hf.2.1,List.map_map]

/-- A satisfying assignment already constant on the actual selected names forwards
UNCHANGED on EVERY natural name, including unused names. Equality is a necessary source
constraint, not inferred from arbitrary values assigned to eliminated output names. -/
theorem forward_closeFirstMetadataRun (sem : Rel → List Bool → Bool) (I : State Rel)
    (a : ℕ) (ks : List ℕ) (hl : (a::ks).length = I.ports.length) (σ : ℕ → Bool)
    (hs : I.body.eval sem σ = true)
    (he : ∀ z ∈ I.ports.take ((a::ks).takeWhile (fun b => decide (b = a))).length,
      σ z = σ (I.ports.headD 0)) :
    ∃ τ : ℕ → Bool, (closeFirstMetadataRun I (a::ks)).body.eval sem τ = true ∧
      (∀ z, τ z = σ z) ∧ (closeFirstMetadataRun I (a::ks)).ports.map τ=
        (I.ports.drop ((a::ks).takeWhile (fun b => decide (b = a))).length).map σ := by
  have hf := fields_closeFirstMetadataRun I a ks hl
  dsimp only at hf
  have ha : (σ ∘ fun z => if z ∈ I.ports.take
      ((a::ks).takeWhile (fun b => decide (b = a))).length then I.ports.headD 0 else z) = σ := by
    funext z
    by_cases hz : z ∈ I.ports.take ((a::ks).takeWhile (fun b => decide (b = a))).length
    · simpa only [Function.comp_apply,ite_eq_left hz] using (he z hz).symm
    · simp only [Function.comp_apply,ite_eq_right hz]
  refine ⟨σ,?_,fun _ => rfl,?_⟩
  · rw [hf.1,CSP.eval_relabel,ha]
    exact hs
  · rw [hf.2.1,List.map_map]
    exact congrArg (fun k =>
      (I.ports.drop ((a::ks).takeWhile (fun b => decide (b = a))).length).map k) ha

end Cslib.Complexity.CSP.CrossInsertion
