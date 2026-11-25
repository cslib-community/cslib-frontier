/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.CyclicDifference.Program

/-!
# Consecutive white-face parity chains

The actual compiler allocates consecutive blocks by prefix sums of actual boundary lengths.
These lemmas compose the checked single-chain semantics while preserving all reserved names.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Cslib.BitString

/-- Prefix allocation after the first face adds just that face's actual auxiliary count. -/
theorem auxiliaryPrefix_cons (scope : List ℕ) (scopes : List (List ℕ)) (i : ℕ) :
    auxiliaryPrefix (scope :: scopes) (i + 1) =
      scope.length - 3 + auxiliaryPrefix scopes i := by
  simp [auxiliaryPrefix]

/-- Recursive specification of the actual zip-index/prefix-sum implementation. -/
theorem whiteConstraints_cons (edges : ℕ) (scope : List ℕ) (scopes : List (List ℕ)) :
    whiteConstraints edges (scope :: scopes) =
      parityChain edges scope ++ whiteConstraints (edges + (scope.length - 3)) scopes := by
  simp only [whiteConstraints, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map,
    auxiliaryPrefix, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero]
  refine congrArg _ (List.flatMap_congr fun ⟨s, i⟩ _ => ?_)
  change parityChain (edges + ((scope :: scopes).take (i + 1) |>.map
    (fun s => s.length - 3)).sum) s = _
  simp only [List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Restriction of any satisfying white expansion enforces every original face parity. -/
theorem whiteConstraints_sound (edges : ℕ) (scopes : List (List ℕ)) (σ : ℕ → Bool)
    (h : (whiteConstraints edges scopes).eval sem σ = true) :
    ∀ scope ∈ scopes, wordParity (scope.map σ) = false := by
  induction scopes generalizing edges with
  | nil => simp
  | cons scope scopes ih =>
    rw [whiteConstraints_cons] at h
    simp only [CSP.eval, List.all_append, Bool.and_eq_true] at h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact parityChain_sound edges _ σ h.1
    · exact ih _ h.2 s hs

/-- Even boundary assignments extend to the whole actual expansion, preserving every reserved
name. Allocation is performed face by face with the exact prefix-sum offsets. -/
theorem whiteConstraints_complete (edges : ℕ) (scopes : List (List ℕ)) (σ : ℕ → Bool)
    (hbound : ∀ scope ∈ scopes, ∀ v ∈ scope, v < edges)
    (hparity : ∀ scope ∈ scopes, wordParity (scope.map σ) = false) :
    ∃ τ : ℕ → Bool, (∀ v < edges, τ v = σ v) ∧
      (whiteConstraints edges scopes).eval sem τ = true := by
  induction scopes generalizing edges σ with
  | nil => exact ⟨σ, fun _ _ => rfl, rfl⟩
  | cons scope scopes ih =>
    obtain ⟨σ', hkeep, heval⟩ := parityChain_complete edges scope σ
      (hbound scope (by simp)) (hparity scope (by simp))
    have hread (v : ℕ) (hv : v < edges) : σ' v = σ v := hkeep v (.inl hv)
    obtain ⟨τ, hτ, hrest⟩ := ih (edges + (scope.length - 3)) σ'
      (fun s hs v hv =>
        (hbound s (List.mem_cons_of_mem _ hs) v hv).trans_le (Nat.le_add_right _ _))
      (fun s hs => by
        rw [List.map_congr_left fun v hv => hread v (hbound s (List.mem_cons_of_mem _ hs) v hv)]
        exact hparity s (List.mem_cons_of_mem _ hs))
    refine ⟨τ, fun v hv => (hτ v (hv.trans_le (Nat.le_add_right _ _))).trans (hread v hv), ?_⟩
    rw [whiteConstraints_cons]
    have hfirst : (parityChain edges scope).eval sem τ = true := by
      rwa [CSP.eval_congr fun v hv => hτ v
        (parityChain_names_lt edges scope (hbound scope (by simp)) v hv)]
    simpa only [CSP.eval, List.all_append, Bool.and_eq_true] using ⟨hfirst, hrest⟩

/-- Complete occurrence accounting for consecutive parity-chain blocks. -/
theorem count_vars_whiteConstraints (edges : ℕ) (scopes : List (List ℕ)) (v : ℕ) :
    (whiteConstraints edges scopes).vars.count v = scopes.flatten.count v +
      if edges ≤ v ∧ v < edges + auxiliaryPrefix scopes scopes.length then 2 else 0 := by
  induction scopes generalizing edges with
  | nil => simp [whiteConstraints, CSP.vars, auxiliaryPrefix]
  | cons scope scopes ih =>
    have hvars : (parityChain edges scope ++
          whiteConstraints (edges + (scope.length - 3)) scopes).vars =
        (parityChain edges scope).vars ++
          (whiteConstraints (edges + (scope.length - 3)) scopes).vars := by
      simp only [CSP.vars, List.flatMap_append]
    rw [whiteConstraints_cons, hvars, List.count_append, count_vars_parityChain, ih]
    simp only [List.flatten_cons, List.count_append, List.length_cons, auxiliaryPrefix_cons]
    split_ifs <;> omega

/-- Every expanded white constraint has a duplicate-free scope when the original white
boundaries are distinct and all old edge names precede the auxiliary blocks. -/
theorem whiteConstraints_scopes_nodup (edges : ℕ) (scopes : List (List ℕ))
    (hnd : ∀ scope ∈ scopes, scope.Nodup)
    (hbound : ∀ scope ∈ scopes, ∀ v ∈ scope, v < edges)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ whiteConstraints edges scopes) :
    constraint.scope.Nodup := by
  induction scopes generalizing edges with
  | nil => simp [whiteConstraints] at hc
  | cons scope scopes ih =>
    rw [whiteConstraints_cons] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact parityChain_scopes_nodup edges scope (hnd scope (by simp))
        (hbound scope (by simp)) constraint hc
    · exact ih _ (fun s hs => hnd s (List.mem_cons_of_mem scope hs))
        (fun s hs v hv =>
          (hbound s (List.mem_cons_of_mem scope hs) v hv).trans_le (Nat.le_add_right _ _)) hc

end Cslib.Complexity.CSP.CyclicCompiler
