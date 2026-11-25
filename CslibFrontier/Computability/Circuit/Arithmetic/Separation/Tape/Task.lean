/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Automata.Weighted.Loop
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import CslibFrontier.Foundations.Data.List.WordsLe

/-!
# Tasks on tape and input channels

A program is a series on the channels `"side b of tape s"` and `"input j"` (`Tape.Ch S J`). Its
value at an input `u` is the sum, over all contents `W` of the tapes of total length at most `t`,
of the weight of the program putting the same word `W s` on both sides of each tape `s`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Task`.

## Main definitions

* `Tape.Ch`, `Tape.chSumEquiv`: tape and input channels, equivalent to `(S × Bool) ⊕ J`.
* `Tape.tup`: channel word assignment matching both sides of every tape.
* `Tape.contents`: finite set of tape contents of total length at most `t`.
* `Tape.val`: value of a program at an input `u` with tape budget `t`.
* `Tape.Bdd`: all contributing tape contents have total length at most `t`.

## Main results

* `Tape.mem_contents`, `Tape.val_eq_of_bdd`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset Cslib.Automata.Weighted

/-- Channels: the two sides of each tape `s : S`, and the inputs `j : J`. -/
inductive Ch (S J : Type*) where
  /-- a side (`false`/`true`) of a tape `s` -/
  | tp (s : S) (b : Bool)
  /-- an input channel `j` -/
  | inp (j : J)
  deriving DecidableEq

/-- Channels as a disjoint sum `(S × Bool) ⊕ J`. -/
@[expose] def chSumEquiv (S J : Type*) : Ch S J ≃ (S × Bool) ⊕ J where
  toFun
    | .tp s b => Sum.inl (s, b)
    | .inp j => Sum.inr j
  invFun
    | Sum.inl (s, b) => .tp s b
    | Sum.inr j => .inp j
  left_inv z := by cases z <;> rfl
  right_inv x := by rcases x with ⟨s, b⟩ | j <;> rfl

instance instFintypeCh {S J : Type*} [Fintype S] [Fintype J] : Fintype (Ch S J) :=
  Fintype.ofEquiv ((S × Bool) ⊕ J) (chSumEquiv S J).symm

/-- The words on the channels for given tape contents `W` and inputs `u`. -/
@[expose] def tup {Γ S J : Type*} (W : S → List Γ) (u : J → List Γ) : Ch S J → List Γ
  | .tp s _ => W s
  | .inp j => u j

/-- The finite set of tape contents of total length at most `t`. -/
@[expose] noncomputable def contents (S Γ : Type*) [Fintype S] [DecidableEq S] [Finite Γ]
    (t : ℕ) : Finset (S → List Γ) :=
  open Classical in
  (Fintype.piFinset fun _ => List.wordsLe Γ t).filter
    fun W => ∑ s, (W s).length ≤ t

theorem mem_contents {S Γ : Type*} [Fintype S] [DecidableEq S] [Finite Γ]
    {t : ℕ} {W : S → List Γ} :
    W ∈ contents S Γ t ↔ ∑ s, (W s).length ≤ t := by
  classical
  simp only [contents, Finset.mem_filter, Fintype.mem_piFinset, List.mem_wordsLe]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun s => ?_, h⟩
    exact (Finset.single_le_sum (f := fun s => (W s).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s)).trans h

section Val

variable {F : Type*} [CommRing F] {Γ : Type*} [Finite Γ]
variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

/-- The value of a program, summed over tape contents of total length at most `t`. -/
@[expose] noncomputable def val (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : F :=
  ∑ W ∈ contents S Γ t, hat P (tup W u)

/-- All tape contents that contribute have total length at most `t`. -/
@[expose] def Bdd (t : ℕ) (P : Series F (Ch S J × Γ)) (u : J → List Γ) : Prop :=
  ∀ W, hat P (tup W u) ≠ 0 → ∑ s, (W s).length ≤ t

theorem val_eq_of_bdd {t t' : ℕ} {P : Series F (Ch S J × Γ)} {u : J → List Γ}
    (h : Bdd t P u) (ht : t ≤ t') : val t' P u = val t P u := by
  classical
  symm
  apply Finset.sum_subset
  · intro W hW
    rw [mem_contents] at hW ⊢
    exact hW.trans ht
  · intro W _ hW
    by_contra hne
    exact hW (mem_contents.2 (h W hne))

end Val

end Cslib.Circuits.Arithmetic.Separation.Tape
