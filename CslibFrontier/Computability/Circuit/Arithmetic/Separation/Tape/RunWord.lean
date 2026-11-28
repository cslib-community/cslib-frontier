/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ReduceOption

/-!
# Places of letters in runs and in the code of the inputs

Emission indexing along a channel (`Tape.emit_getElem`, `Tape.exists_emit`) and the
separator-delimited concatenation encoding `Tape.wordOf` / one-hot code `Tape.code` of a tuple
of input words.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.RunWord`.

## Main definitions

* `Tape.wordOf`: concatenate words separated by trailing `none` markers.
* `Tape.base`: starting offset of input word `k` inside `wordOf (List.ofFn u)`.
* `Tape.code`: one-hot boolean encoding of `wordOf (List.ofFn u)`.

## Main results

* `Tape.emit_getElem`, `Tape.exists_emit`: relating emitted letters to run step indices.
* `Tape.eq_of_read`: reading `wordOf (List.ofFn u)` at every position of `v` determines `u = v`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Cslib.Automata.Weighted

section Emit

variable {Γ S J : Type*} [DecidableEq S] [DecidableEq J]

theorem emit_appendR (o o' : List (Letter S J Γ)) (z : Ch S J) :
    emit (o ++ o') z = emit o z ++ emit o' z := by
  unfold emit
  rw [List.reduceOption_append, proj_append]

@[simp] theorem emit_nil (z : Ch S J) : emit ([] : List (Letter S J Γ)) z = [] := rfl

@[simp] theorem emit_none (z : Ch S J) : emit ([none] : List (Letter S J Γ)) z = [] := rfl

theorem emit_some (z z' : Ch S J) (γ : Γ) :
    emit ([some (z', γ)] : List (Letter S J Γ)) z = if z' = z then [γ] else [] := by
  unfold emit
  rw [List.reduceOption_cons_of_some, List.reduceOption_nil, proj_cons, proj_nil]

theorem emit_length_le (o : List (Letter S J Γ)) (z : Ch S J) :
    (emit o z).length ≤ o.length := by
  induction o with
  | nil => simp
  | cons a o ih =>
    rw [← List.singleton_append, emit_appendR, List.length_append, List.length_append]
    have hstep : (emit [a] z).length ≤ 1 := by
      rcases a with _ | ⟨z', γ⟩
      · simp
      · rw [emit_some]
        split_ifs <;> simp
    simpa using Nat.add_le_add hstep ih

/-- The letter emitted at a step sits at the position counted before that step. -/
theorem emit_getElem (o : List (Letter S J Γ)) (z : Ch S J) (τ : ℕ) (γ : Γ)
    (h : o[τ]? = some (some (z, γ))) :
    (emit o z)[(emit (o.take τ) z).length]? = some γ := by
  have hτ : τ < o.length := (List.getElem?_eq_some_iff.1 h).1
  have ho : o = o.take τ ++ ([some (z, γ)] ++ o.drop (τ + 1)) := by
    conv_lhs => rw [← List.take_append_drop τ o, List.drop_eq_getElem_cons hτ]
    rw [(List.getElem?_eq_some_iff.1 h).2]
    rfl
  conv_lhs => rw [ho]
  rw [emit_appendR, emit_appendR, emit_some, ite_eq_left rfl,
    List.take_append_of_le_length (by simp; omega),
    List.take_take, min_self, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

/-- Every letter of a channel is emitted at some step. -/
theorem exists_emit (o : List (Letter S J Γ)) (z : Ch S J) (p : ℕ)
    (hp : p < (emit o z).length) :
    ∃ τ γ, τ < o.length ∧ o[τ]? = some (some (z, γ)) ∧ (emit (o.take τ) z).length = p := by
  induction o using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton o a ih =>
    by_cases h : p < (emit o z).length
    · obtain ⟨τ, γ, h1, h2, h3⟩ := ih h
      refine ⟨τ, γ, by simp; omega, ?_, ?_⟩
      · rw [List.getElem?_append_left h1, h2]
      · rw [List.take_append_of_le_length h1.le, h3]
    · rw [emit_appendR, List.length_append] at hp
      rcases a with _ | ⟨z', γ⟩
      · simp at hp
        omega
      · rw [emit_some] at hp
        split_ifs at hp with hz
        · subst hz
          refine ⟨o.length, γ, by simp, by simp, ?_⟩
          rw [List.take_append_of_le_length le_rfl, List.take_length]
          simp at hp
          omega
        · simp at hp
          omega

end Emit

section Code

variable {Γ : Type*}

/-- Concatenate words one after another, each followed by a `none` separator. -/
@[expose] def wordOf (v : List (List Γ)) : List (Option Γ) :=
  v.flatMap fun l => l.map some ++ [none]

theorem wordOf_cons (l : List Γ) (v : List (List Γ)) :
    wordOf (l :: v) = l.map some ++ none :: wordOf v := by
  simp [wordOf]

theorem wordOf_append (v v' : List (List Γ)) : wordOf (v ++ v') = wordOf v ++ wordOf v' := by
  simp [wordOf]

theorem length_wordOf (v : List (List Γ)) :
    (wordOf v).length = (v.map List.length).sum + v.length := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    rw [wordOf_cons]
    simp [ih]
    omega

variable {n : ℕ}

/-- The starting offset of the `k`-th input word in `wordOf (List.ofFn u)`. -/
@[expose] def base (u : Fin n → List Γ) (k : ℕ) : ℕ :=
  (wordOf ((List.ofFn u).take k)).length

@[simp] theorem base_zero (u : Fin n → List Γ) : base u 0 = 0 := by simp [base, wordOf]

theorem base_succ (u : Fin n → List Γ) (k : Fin n) :
    base u (k + 1) = base u k + (u k).length + 1 := by
  unfold base
  rw [List.take_add_one, wordOf_append, List.length_append]
  simp [wordOf]
  omega

private theorem ofFn_split (u : Fin n → List Γ) (k : Fin n) :
    List.ofFn u = (List.ofFn u).take k ++ u k :: (List.ofFn u).drop (k + 1) := by
  conv_lhs => rw [← List.take_append_drop k (List.ofFn u), List.drop_eq_getElem_cons (by simp)]
  simp

theorem wordOf_getElem (u : Fin n → List Γ) (k : Fin n) (p : ℕ) :
    (wordOf (List.ofFn u))[base u k + p]? =
      ((u k).map some ++ none :: wordOf ((List.ofFn u).drop (k + 1)))[p]? := by
  conv_lhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.getElem?_append_right (by simp [base])]
  simp [base]

theorem base_add_lt (u : Fin n → List Γ) (k : Fin n) :
    base u k + (u k).length < (wordOf (List.ofFn u)).length := by
  conv_rhs => rw [ofFn_split u k]
  rw [wordOf_append, wordOf_cons, List.length_append, List.length_append,
    List.length_cons, List.length_map]
  unfold base
  omega

private theorem eq_of_prefix (l m : List Γ) (r : List (Option Γ))
    (h : ∀ p ≤ m.length, (l.map some ++ none :: r)[p]? = (m.map some ++ [none])[p]?) :
    l = m := by
  induction m generalizing l with
  | nil => cases l with | nil => rfl | cons a l => simpa using h 0 (by simp)
  | cons b m ih =>
    cases l with
    | nil => simpa using h 0 (by simp)
    | cons a l =>
      obtain rfl : a = b := by simpa using h 0 (by simp)
      exact congrArg (a :: ·) (ih l fun p hp => by simpa using h (p + 1) (by simpa using hp))

/-- A code that agrees with `v` at all positions of `v` represents `v`. -/
theorem eq_of_read (u v : Fin n → List Γ)
    (h : ∀ k : Fin n, ∀ p ≤ (v k).length,
      (wordOf (List.ofFn u))[base v k + p]? = ((v k).map some ++ [none])[p]?) :
    u = v := by
  have key : ∀ m : ℕ, ∀ k : Fin n, k.val = m → u k = v k := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rintro k rfl
      have hb : base u k = base v k := by
        unfold base
        congr 2
        apply List.ext_getElem
        · simp
        · intro i h1 _
          simp only [List.getElem_take, List.getElem_ofFn]
          simp only [List.length_take, List.length_ofFn] at h1
          exact ih i (by omega) _ rfl
      refine eq_of_prefix (u k) (v k) (wordOf ((List.ofFn u).drop (k + 1))) fun p hp => ?_
      rw [← wordOf_getElem, hb, h k p hp]
  exact funext fun k => key k k rfl

/-- The one-hot Boolean encoding of the separator-delimited input words. -/
@[expose] def code [DecidableEq Γ] (N : ℕ) (u : Fin n → List Γ) :
    Fin N × Option Γ → Bool
  | (pos, sym) => decide ((wordOf (List.ofFn u))[pos.val]? = some sym)

end Code

end Cslib.Circuits.Arithmetic.Separation.Tape
