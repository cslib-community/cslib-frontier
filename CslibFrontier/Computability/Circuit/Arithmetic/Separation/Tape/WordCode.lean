/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunSum
import Mathlib.Tactic.DeriveFintype

/-!
# The one-hot code of a word, and clauses that allow only codes

The code of a word `u` on `N` places sets the bit `(p, y)` when the letter at place `p` of `u`
followed by an end mark is `y` (`Tape.wordCode`). A family of bits is a code
(`Tape.IsWordCode`) if every place has at most one letter, and every place has a letter unless the
end mark came before; below the code of `u` only that code is one (`Tape.eq_wordCode`), and a code
has at most `N` set bits (`Tape.card_ones_le`). Clauses on the input bits (`Tape.CodeRule`) allow
only codes (`Tape.prod_codeLits`), so adding them to a clause sum restricts it to codes
(`Tape.domainClauseSum_codeLits`).

## Main definitions

* `Tape.wordCode`, `Tape.IsWordCode`, `Tape.CodeRule`, `Tape.codeLits`, `Tape.codeWeights`.

## Main results

* `Tape.isWordCode_wordCode`, `Tape.eq_wordCode`, `Tape.card_ones_le`, `Tape.card_ones_wordCode`.
* `Tape.prod_codeLits`, `Tape.domainClauseSum_codeLits`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Nc.RunOne` (`code1`) and `Nc.RunMn`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset

section Code

variable {Γ : Type} {N : ℕ}

/-- The one-hot code of a word with an end mark: bit `(p, y)` is set when the letter at place `p` of
`u` followed by the end mark `none` is `y`. -/
@[expose] def wordCode [DecidableEq Γ] (N : ℕ) (u : List Γ) (b : Fin N × Option Γ) : Bool :=
  (u.map some ++ [none])[(b.1 : ℕ)]? = some b.2

/-- At most one letter at each place, and at each place a letter or an end mark before. -/
structure IsWordCode (x : Fin N × Option Γ → Bool) : Prop where
  /-- at most one letter at each place -/
  unique : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
  /-- a letter at each place, unless the end mark came before -/
  exists_of_le : ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true

theorem isWordCode_iff (x : Fin N × Option Γ → Bool) : IsWordCode x ↔
    (∀ p y y', x (p, y) = true → x (p, y') = true → y = y') ∧
      ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance [Fintype Γ] [DecidableEq Γ] : DecidablePred (IsWordCode (Γ := Γ) (N := N)) :=
  fun x => decidable_of_iff _ (isWordCode_iff x).symm

variable [DecidableEq Γ]

private theorem wordCode_eq {u : List Γ} {p : Fin N} {y : Option Γ}
    (h : wordCode N u (p, y) = true) : (u.map some ++ [none])[p.1]? = some y := by
  simpa [wordCode] using h

private theorem le_length_of_wordCode {u : List Γ} {p : Fin N} {y : Option Γ}
    (h : wordCode N u (p, y) = true) : p.1 ≤ u.length := by
  have := (List.getElem?_eq_some_iff.1 (wordCode_eq h)).1
  simp only [List.length_append, List.length_map, List.length_singleton] at this; omega

private theorem wordCode_unique {u : List Γ} {p : Fin N} {y y' : Option Γ}
    (h : wordCode N u (p, y) = true) (h' : wordCode N u (p, y') = true) : y = y' :=
  Option.some.inj <| (wordCode_eq h).symm.trans (wordCode_eq h')

theorem isWordCode_wordCode (u : List Γ) : IsWordCode (wordCode N u) := by
  refine ⟨fun _ _ _ => wordCode_unique, fun p => ?_⟩
  by_cases hp : p.1 ≤ u.length
  · have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
    exact Or.inl ⟨(u.map some ++ [none])[p.1], by simp [wordCode, List.getElem?_eq_getElem hlt]⟩
  · exact Or.inr ⟨⟨u.length, by omega⟩, show u.length < p.1 by omega, by simp [wordCode]⟩

/-- Below the code of a word only this code is a code. -/
theorem eq_wordCode {x : Fin N × Option Γ → Bool} (hx : IsWordCode x) {u : List Γ}
    (hle : ∀ b, x b = true → wordCode N u b = true) : x = wordCode N u := by
  funext ⟨p, y⟩
  rcases hc : wordCode N u (p, y) with _ | _
  · exact Bool.eq_false_iff.2 fun h => by rw [hle _ h] at hc; cases hc
  · rcases hx.exists_of_le p with ⟨y', hy'⟩ | ⟨p', hp', h'⟩
    · exact wordCode_unique hc (hle _ hy') ▸ hy'
    · have h1 := wordCode_eq (hle _ h')
      rcases (le_length_of_wordCode (hle _ h')).lt_or_eq with hlt | heq
      · rw [List.getElem?_append_left (by simpa using hlt)] at h1; simp at h1
      · have := le_length_of_wordCode hc; rw [Fin.lt_def] at hp'; omega

variable [Fintype Γ]

omit [DecidableEq Γ] in
/-- A code has at most one set bit per place. -/
theorem card_ones_le {x : Fin N × Option Γ → Bool} (hx : IsWordCode x) :
    #{b | x b = true} ≤ N := by
  simpa using card_le_card_of_injOn (s := {b | x b = true}) (t := univ) Prod.fst
    (fun _ _ => mem_univ _) fun ⟨p, y⟩ h ⟨p', y'⟩ h' e => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h h' e
      subst e; exact Prod.ext rfl (hx.unique p y y' h h')

theorem card_ones_wordCode (u : List Γ) (hu : u.length + 1 ≤ N) :
    #{b | wordCode N u b = true} = u.length + 1 := by
  symm
  simpa using card_bij (s := univ (α := Fin (u.length + 1)))
    (t := {b : Fin N × Option Γ | wordCode N u b = true})
    (fun k _ => (⟨k.1, by omega⟩, (u.map some ++ [none])[k.1]'(by simp)))
    (fun k _ => by simp [wordCode])
    (fun k _ k' _ e => Fin.ext (congrArg (fun b => b.1.1) e))
    fun ⟨p, y⟩ h => by
      simp only [mem_filter, mem_univ, true_and] at h
      have h2 := le_length_of_wordCode h
      have hlt : p.1 < (u.map some ++ [none]).length := by simp; omega
      have h1 := wordCode_eq h; rw [List.getElem?_eq_getElem hlt] at h1
      exact ⟨⟨p.1, by omega⟩, mem_univ _, by simp [Option.some.inj h1]⟩

end Code

section Rules

variable {F : Type*} [CommSemiring F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [DecidableEq S]
  [DecidableEq Q] {n t M N : ℕ}

/-- The clauses on the input bits. -/
inductive CodeRule (Γ : Type) (N : ℕ) where
  /-- two letters at one place -/
  | symbol (p : Fin N) (y y' : Option Γ)
  /-- no letter at a place, and no end mark before -/
  | missing (p : Fin N)
  deriving DecidableEq, Fintype

/-- `CodeRule` as a sum. -/
@[expose] def CodeRule.equivSum (Γ : Type) (N : ℕ) :
    CodeRule Γ N ≃ (Fin N × Option Γ × Option Γ) ⊕ Fin N where
  toFun
    | .symbol p y y' => .inl (p, y, y')
    | .missing p => .inr p
  invFun
    | .inl (p, y, y') => .symbol p y y'
    | .inr p => .missing p
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with ⟨_, _, _⟩ | _ <;> rfl

/-- Their literals. -/
@[expose] noncomputable def codeLits : CodeRule Γ N → List (RunBit Γ S Q n t M N × Bool)
  | .symbol p y y' => [(.inl (p, y), true), (.inl (p, y'), true)]
  | .missing p => ((univ : Finset (Option Γ)).toList.map fun y => (.inl (p, y), false)) ++
      ((univ : Finset (Fin N)).filter (· < p)).toList.map fun p' => (.inl (p', none), false)

/-- Their weights: `0`, except for two equal letters. -/
@[expose] def codeWeights : CodeRule Γ N → F
  | .symbol _ y y' => if y = y' then 1 else 0
  | .missing _ => 0

/-- **The clauses on the input bits allow only codes.** -/
theorem prod_codeLits (x : Fin N × Option Γ → Bool)
    (g : RunAssignment Γ S Q n t M) :
    (∏ r : CodeRule Γ N, if ∀ l ∈ codeLits (S := S) (Q := Q) (n := n) (t := t) (M := M) r,
        Sum.elim x (Pi.oneHot g) l.1 = l.2 then (codeWeights r : F) else 1) =
      if IsWordCode x then 1 else 0 := by
  rw [← (CodeRule.equivSum Γ N).symm.prod_comp, Fintype.prod_sum_type]
  simp only [CodeRule.equivSum, Equiv.coe_fn_symm_mk]
  split_ifs with hx
  · rw [prod_eq_one, prod_eq_one, one_mul]
    · intro p _
      refine ite_eq_right fun h => ?_
      rcases hx.exists_of_le p with ⟨y, hy⟩ | ⟨p', hp', h'⟩
      · simpa [hy] using h (.inl (p, y), false) (by simp [codeLits])
      · simpa [h'] using h (.inl (p', none), false) (by simp [codeLits, hp'])
    · rintro ⟨p, y, y'⟩ _
      by_cases h : ∀ l ∈ codeLits (S := S) (Q := Q) (n := n) (t := t) (M := M)
          (CodeRule.symbol p y y'), Sum.elim x (Pi.oneHot g) l.1 = l.2
      · simp only [codeLits, List.forall_mem_cons, Sum.elim_inl] at h
        exact (ite_eq_left (by simp [codeLits, h.1, h.2.1])).trans
          (ite_eq_left (hx.unique p y y' h.1 h.2.1))
      · exact ite_eq_right h
  · by_cases h1 : ∀ p y y', x (p, y) = true → x (p, y') = true → y = y'
    · have h2 : ¬ ∀ p, (∃ y, x (p, y) = true) ∨ ∃ p' < p, x (p', none) = true :=
        fun h => hx ⟨h1, h⟩
      push Not at h2; obtain ⟨p, h3, h4⟩ := h2
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ p) ((ite_eq_left ?_).trans rfl))
      intro l hl
      simp only [codeLits, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and,
        mem_filter] at hl
      rcases hl with ⟨y, rfl⟩ | ⟨p', hp', rfl⟩ <;> [simpa using h3 y; simpa using h4 p' hp']
    · push Not at h1; obtain ⟨p, y, y', h3, h4, hne⟩ := h1
      refine mul_eq_zero_of_left ?_ _
      exact prod_eq_zero (mem_univ (p, y, y'))
        ((ite_eq_left (by simp [codeLits, h3, h4])).trans (ite_eq_right hne))

/-- **Adding the clauses on the input bits restricts a clause sum to codes.** -/
theorem domainClauseSum_codeLits [Fintype S] [Fintype Q] {Θ : Type} [Fintype Θ]
    (lits : Θ → List (RunBit Γ S Q n t M N × Bool)) (w : Θ → F) (x : Fin N × Option Γ → Bool) :
    domainClauseSum (Sum.elim lits codeLits) (Sum.elim w (codeWeights : CodeRule Γ N → F)) x =
      if IsWordCode x then domainClauseSum lits w x else 0 := by
  rw [domainClauseSum_sumElim lits w codeLits codeWeights x (if IsWordCode x then 1 else 0)]
  · split_ifs <;> simp
  · exact prod_codeLits (F := F) x

end Rules

end Cslib.Circuits.Arithmetic.Separation.Tape
