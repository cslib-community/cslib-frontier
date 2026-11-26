/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Table.DeltaMatroid
public import CslibFrontier.Foundations.Data.BitString.Enumeration
public import CslibFrontier.Foundations.Data.BitString.ListParity
import Mathlib.Data.List.GetD

/-!
# Explicit parity chains

The chain replaces an EVEN constraint by tables of width at most three. It has `k - 2`
constraints and `k - 3` fresh variables when `k ≥ 4`; smaller scopes retain one table.
Fresh names begin at the supplied offset. Construction traverses the actual scope, never
an unchecked binary arity. The chain is an original implementation detail for the difference
reduction of [DvorakKupec2015], Section 3, Lemma 5, Corollary 4 and Theorem 2,
printed pp. 439–440. No geometric realization of the expansion is asserted or needed.

## Main definitions

* `Cslib.Logic.PL.CSP.Table.evenTable`: explicit even-parity rows.
* `Cslib.Logic.PL.CSP.Table.parityChain`: the actual width-three expansion.
-/

public section

namespace Cslib.Logic.PL.CSP.Table

open Cslib.BitString

/-- Explicit even-parity table. Only widths zero through three are generated at runtime by
`parityChain`; larger tables are a mathematical API, with no uniform polynomial claim. -/
@[expose] def evenTable (width : ℕ) : Table :=
  ⟨width, (enumList width).filter fun row => !wordParity row⟩

@[simp] theorem arity_evenTable (width : ℕ) : (evenTable width).arity = width := rfl

/-- Every row has exactly the declared width, including the nullary row. -/
theorem wellFormed_evenTable (width : ℕ) : (evenTable width).wellFormed = true := by
  exact wellFormed_eq_true.mpr fun _ hrow => length_of_mem_enumList (List.mem_filter.mp hrow).1

/-- The table includes the exact-arity guard even for malformed supplied rows. -/
theorem sem_evenTable (width : ℕ) (row : List Bool) :
    (evenTable width).sem row = true ↔ row.length = width ∧ wordParity row = false := by
  rw [sem_eq_true, wellFormed_evenTable]
  simp [evenTable, mem_enumList]

/-- Explicit tables denote the existing parity relation, without a second Boolean model. -/
theorem booleanRelation_evenTable (width : ℕ) :
    booleanRelation arity sem (evenTable width) =
      {x : Fin width → Bool | parityOn Finset.univ x = false} := by
  simp only [booleanRelation, sem_evenTable, arity_evenTable, List.length_ofFn, wordParity_ofFn,
    true_and]

/-- All parity tables used by a chain are nonempty even delta-matroids. -/
theorem isEvenDeltaMatroid_evenTable (width : ℕ) :
    IsEvenDeltaMatroid (booleanRelation arity sem (evenTable width)) := by
  rw [booleanRelation_evenTable]
  exact isEvenDeltaMatroid_parityOn_fiber false
    ⟨fun _ => false, (parityOn_eq_sum _ _).trans Finset.sum_const_zero⟩

/-- Chain tail with the accumulated parity variable first. Each recursive step consumes one
actual boundary entry and allocates one fresh binary name. -/
@[expose] def parityChainTail (fresh first : ℕ) : List ℕ → CSP Table ℕ
  | [] => [⟨evenTable 1, [first]⟩]
  | [b] => [⟨evenTable 2, [first, b]⟩]
  | [b, c] => [⟨evenTable 3, [first, b, c]⟩]
  | b :: c :: d :: rest =>
    ⟨evenTable 3, [first, b, fresh]⟩ :: parityChainTail (fresh + 1) fresh (c :: d :: rest)

/-- Width-three expansion, retaining the original boundary order. Names below `fresh` are
reserved for the caller; an empty boundary is the true nullary parity table. -/
@[expose] def parityChain (fresh : ℕ) (scope : List ℕ) : CSP Table ℕ :=
  match scope with
  | [] => [⟨evenTable 0, []⟩]
  | first :: rest => parityChainTail fresh first rest

/-- Exactly the requested number of chain constraints. -/
theorem length_parityChainTail (fresh first : ℕ) (rest : List ℕ) :
    (parityChainTail fresh first rest).length = max 1 (rest.length - 1) := by
  fun_induction parityChainTail fresh first rest with
  | case4 => simp only [List.length_cons] at *; omega -- b :: c :: d :: rest: chain step
  | _ => rfl -- at most two boundary entries left

/-- Linear constraint count, including empty and short boundaries. -/
theorem length_parityChain (fresh : ℕ) (scope : List ℕ) :
    (parityChain fresh scope).length = max 1 (scope.length - 2) := by
  cases scope with
  | nil => rfl
  | cons first rest => simpa [parityChain] using length_parityChainTail fresh first rest

/-- Every output table and scope has matching width at most three. -/
theorem parityChainTail_width (fresh first : ℕ) (rest : List ℕ)
    (c : Constraint Table ℕ) (hc : c ∈ parityChainTail fresh first rest) :
    c.rel.arity = c.scope.length ∧ c.scope.length ≤ 3 ∧
      ∃ n ≤ 3, c.rel = evenTable n := by
  fun_induction parityChainTail fresh first rest with
  | case4 _ _ _ _ _ _ ih => -- b :: c :: d :: rest: chain step
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨rfl, by simp, 3, le_rfl, rfl⟩
    · exact ih hc
  | _ => -- at most two boundary entries left
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨rfl, by simp, _, by omega, rfl⟩

/-- The actual expansion uses only nonempty even delta-matroid relations. -/
theorem parityChain_tables (fresh : ℕ) (scope : List ℕ)
    (c : Constraint Table ℕ) (hc : c ∈ parityChain fresh scope) :
    c.rel.arity = c.scope.length ∧ c.scope.length ≤ 3 ∧
      IsEvenDeltaMatroid (booleanRelation arity sem c.rel) := by
  cases scope with
  | nil =>
    obtain rfl : c = ⟨evenTable 0, []⟩ := by simpa [parityChain] using hc
    exact ⟨rfl, by decide, isEvenDeltaMatroid_evenTable 0⟩
  | cons first rest =>
    obtain ⟨hw, hb, n, _, hn⟩ := parityChainTail_width fresh first rest c hc
    exact ⟨hw, hb, hn ▸ isEvenDeltaMatroid_evenTable n⟩

/-- Every satisfying chain assignment has even boundary parity. This direction needs no
freshness or distinctness assumption, so repeated boundary names cause no semantic shortcut. -/
theorem parityChainTail_sound (fresh first : ℕ) (rest : List ℕ) (σ : ℕ → Bool)
    (h : (parityChainTail fresh first rest).eval sem σ = true) :
    wordParity ((first :: rest).map σ) = false := by
  fun_induction parityChainTail fresh first rest with
  | case4 fresh first b c d rest ih => -- b :: c :: d :: rest: chain step
    simp only [CSP.eval, List.all_cons, Bool.and_eq_true, Constraint.eval] at h
    have hp := (sem_evenTable 3 _).mp h.1 |>.2
    have ht := ih h.2
    simp only [List.map_cons, List.map_nil, wordParity_cons, wordParity_nil,
      Bool.xor_false, bne_eq_false_iff_eq] at hp ht ⊢
    rwa [← ht]
  | _ => -- at most two boundary entries left
    exact (sem_evenTable _ _).mp (by simpa only [CSP.eval, List.all_cons, List.all_nil,
      Bool.and_true, Constraint.eval] using h) |>.2

/-- A satisfying expansion enforces even parity on its original boundary, including zero
and one ports. -/
theorem parityChain_sound (fresh : ℕ) (scope : List ℕ) (σ : ℕ → Bool)
    (h : (parityChain fresh scope).eval sem σ = true) : wordParity (scope.map σ) = false := by
  cases scope with
  | nil => rfl
  | cons first rest => exact parityChainTail_sound fresh first rest σ h

/-- Extend any even boundary assignment using only the consecutive allocated auxiliary block.
Names outside that block are preserved, including arbitrary large binary names. -/
theorem parityChainTail_complete (fresh first : ℕ) (rest : List ℕ) (σ : ℕ → Bool)
    (hbound : ∀ v ∈ first :: rest, v < fresh)
    (hparity : wordParity ((first :: rest).map σ) = false) :
    ∃ τ : ℕ → Bool,
      (∀ v, v < fresh ∨ fresh + (rest.length - 2) ≤ v → τ v = σ v) ∧
      (parityChainTail fresh first rest).eval sem τ = true := by
  fun_induction parityChainTail fresh first rest generalizing σ with
  | case4 fresh first b c d rest ih => -- b :: c :: d :: rest: chain step
    let σ' := Function.update σ fresh (σ first ^^ σ b)
    have hfirst := hbound first (by simp)
    have hb := hbound b (by simp)
    have hread (v : ℕ) (hv : v < fresh) : σ' v = σ v := Function.update_of_ne (by omega) _ _
    have hnext (v : ℕ) (hv : v ∈ fresh :: c :: d :: rest) : v < fresh + 1 :=
      (List.mem_cons.mp hv).elim (fun h => by omega) fun hv =>
        (hbound v (by simp [hv])).trans (Nat.lt_succ_self fresh)
    have hparity' : wordParity ((fresh :: c :: d :: rest).map σ') = false := by
      have he : (c :: d :: rest).map σ' = (c :: d :: rest).map σ :=
        List.map_congr_left fun v hv => hread v (hbound v (by simp [hv]))
      simp only [List.map_cons, wordParity_cons, he, σ', Function.update_self, Bool.xor_assoc]
      exact hparity
    obtain ⟨τ, hτ, heval⟩ := ih σ' hnext hparity'
    refine ⟨τ, fun v hv => ?_, ?_⟩
    · simp only [List.length_cons] at hv
      rw [hτ v (by simp only [List.length_cons]; omega)]
      exact Function.update_of_ne (by omega) _ _
    · simp only [CSP.eval, List.all_cons, Bool.and_eq_true, Constraint.eval]
      refine ⟨(sem_evenTable 3 _).mpr ⟨rfl, ?_⟩, heval⟩
      simp only [List.map_cons, List.map_nil, wordParity_cons, wordParity_nil, Bool.xor_false]
      rw [hτ first (.inl (by omega)), hτ b (.inl (by omega)), hτ fresh (.inl (by omega)),
        hread first hfirst, hread b hb]
      simp only [σ', Function.update_self]
      cases σ first <;> cases σ b <;> rfl
  | _ => -- at most two boundary entries left
    refine ⟨σ, fun _ _ => rfl, ?_⟩
    simp only [CSP.eval, List.all_cons, List.all_nil, Bool.and_true, Constraint.eval]
    exact (sem_evenTable _ _).mpr ⟨rfl, hparity⟩

/-- Exact existential semantics of the actual chain with its allocated names. -/
theorem parityChain_complete (fresh : ℕ) (scope : List ℕ) (σ : ℕ → Bool)
    (hbound : ∀ v ∈ scope, v < fresh) (hparity : wordParity (scope.map σ) = false) :
    ∃ τ : ℕ → Bool,
      (∀ v, v < fresh ∨ fresh + (scope.length - 3) ≤ v → τ v = σ v) ∧
      (parityChain fresh scope).eval sem τ = true := by
  cases scope with
  | nil =>
    refine ⟨σ, fun _ _ => rfl, ?_⟩
    change (evenTable 0).sem [] && true = true
    decide
  | cons first rest =>
    simpa only [parityChain, List.length_cons, Nat.succ_sub_succ_eq_sub] using
      parityChainTail_complete fresh first rest σ hbound hparity

/-- Exactly two occurrences of each allocated auxiliary, and the original multiplicity of
all boundary names. This equality does not assume that the caller chose fresh names. -/
theorem count_vars_parityChainTail (fresh first : ℕ) (rest : List ℕ) (v : ℕ) :
    (parityChainTail fresh first rest).vars.count v = (first :: rest).count v +
      if fresh ≤ v ∧ v < fresh + (rest.length - 2) then 2 else 0 := by
  fun_induction parityChainTail fresh first rest with
  | case4 fresh first b c d rest ih => -- b :: c :: d :: rest: chain step
    change ([first, b, fresh] ++ (parityChainTail (fresh + 1) fresh
      (c :: d :: rest)).vars).count v = _
    rw [List.count_append, ih]
    simp only [List.count_cons, List.count_nil, List.length_cons]
    split_ifs <;> simp_all only [beq_iff_eq] <;> omega
  | _ => simp [CSP.vars] -- at most two boundary entries left

/-- Every old boundary occurrence is retained once, and every new auxiliary occurs twice. -/
theorem count_vars_parityChain (fresh : ℕ) (scope : List ℕ) (v : ℕ) :
    (parityChain fresh scope).vars.count v = scope.count v +
      if fresh ≤ v ∧ v < fresh + (scope.length - 3) then 2 else 0 := by
  cases scope with
  | nil => simp [parityChain, CSP.vars]
  | cons first rest =>
    simpa only [parityChain, List.length_cons, Nat.succ_sub_succ_eq_sub] using
      count_vars_parityChainTail fresh first rest v

/-- Output names are boundary names or precisely the allocated consecutive auxiliary interval. -/
theorem mem_vars_parityChain (fresh : ℕ) (scope : List ℕ) (v : ℕ) :
    v ∈ (parityChain fresh scope).vars ↔
      v ∈ scope ∨ fresh ≤ v ∧ v < fresh + (scope.length - 3) := by
  rw [← List.count_pos_iff, count_vars_parityChain, ← List.count_pos_iff]
  split_ifs <;> omega

/-- The entire output lies below the first unused name when all boundary names are reserved. -/
theorem parityChain_names_lt (fresh : ℕ) (scope : List ℕ)
    (hbound : ∀ v ∈ scope, v < fresh) (v : ℕ)
    (hv : v ∈ (parityChain fresh scope).vars) : v < fresh + (scope.length - 3) := by
  rcases (mem_vars_parityChain fresh scope v).mp hv with hb | ha
  · exact (hbound v hb).trans_le (Nat.le_add_right _ _)
  · exact ha.2

/-- No scope repeats a name when the original boundary is distinct and auxiliaries are fresh. -/
theorem parityChainTail_scopes_nodup (fresh first : ℕ) (rest : List ℕ)
    (hnd : (first :: rest).Nodup) (hbound : ∀ v ∈ first :: rest, v < fresh)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ parityChainTail fresh first rest) :
    constraint.scope.Nodup := by
  fun_induction parityChainTail fresh first rest with
  | case4 fresh first b c d rest ih => -- b :: c :: d :: rest: chain step
    rcases List.mem_cons.mp hc with rfl | hc
    · have hfirst := hbound first (by simp)
      have hb := hbound b (by simp)
      have hne : first ≠ b := fun he => hnd.notMem (by simp [he])
      simp only [List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, not_false_eq_true, and_true]
      exact ⟨⟨hne, by omega⟩, by omega, trivial, List.nodup_nil⟩
    · refine ih (List.nodup_cons.mpr ⟨fun hf => ?_, hnd.tail.tail⟩) (fun v hv => ?_) hc
      · have := hbound fresh (by simp [hf])
        omega
      · rcases List.mem_cons.mp hv with rfl | hv
        · omega
        · exact (hbound v (by simp [hv])).trans (Nat.lt_succ_self fresh)
  | _ => -- at most two boundary entries left
    obtain rfl := List.mem_singleton.mp hc
    exact hnd

/-- Fresh parity expansion satisfies the target's no-repeat-within-one-scope convention. -/
theorem parityChain_scopes_nodup (fresh : ℕ) (scope : List ℕ) (hnd : scope.Nodup)
    (hbound : ∀ v ∈ scope, v < fresh)
    (constraint : Constraint Table ℕ) (hc : constraint ∈ parityChain fresh scope) :
    constraint.scope.Nodup := by
  cases scope with
  | nil =>
    obtain rfl : constraint = ⟨evenTable 0, []⟩ := by simpa [parityChain] using hc
    exact List.nodup_nil
  | cons first rest => exact parityChainTail_scopes_nodup fresh first rest hnd hbound constraint hc

end Cslib.Logic.PL.CSP.Table
