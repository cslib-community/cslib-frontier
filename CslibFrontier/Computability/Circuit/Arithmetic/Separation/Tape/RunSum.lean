/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunGood
public import CslibFrontier.Computability.Circuit.Arithmetic.ClauseSum
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

/-!
# The certificates of a run as an assignment on a finite domain

A certificate of a run of a multi-tape automaton (M1's `Tape.Good`) consists of the letters, the
states, the head places and the tape contents. Here they are one function `g : RunAssignment` on
the finite domain `RunVar`: a letter for every step, a state for every time, a place for every
channel and time, and a content for every tape cell. Its one-hot bits, together with the code bits
of the input, are the bits `RunBit` of a clause sum.

Two families of clauses check a certificate:
* the weighted clauses `RunStep`, one per step, letter and pair of states, carry the matrix entry
  of the step (`prod_stepLits`);
* the forbidding clauses `RunRule`, with weight `0` when they are in force (`RunRule.InForce`),
  forbid exactly the assignments that are no certificate (`respectsRules_iff_good`,
  `prod_ruleLits`).

## Main definitions

* `Tape.RunVar`, `Tape.RunVar.Dom`, `Tape.RunAssignment`, `Tape.RunBit`.
* `Tape.RunStep`, `Tape.RunRule`, `Tape.stepLits`, `Tape.ruleLits`, `Tape.RunRule.InForce`.
* `Tape.RespectsRules`, `Tape.runLits`, `Tape.runWeights`.

## Main results

* `Tape.respectsRules_iff_good`, `Tape.prod_stepLits`, `Tape.prod_ruleLits`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.RunSum`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset

variable {F : Type*} [CommSemiring F] {Γ S Q : Type} [DecidableEq Γ] [DecidableEq S]
  [DecidableEq Q]
  {n t M N : ℕ}

/-- The hidden variables of a certificate: a letter for every step, a state for every time, a place
for every channel and time, and a content for every tape cell. -/
inductive RunVar (S : Type) (n t M : ℕ) where
  /-- the letter of step `τ` -/
  | letter (τ : Fin t)
  /-- the state at time `τ` -/
  | state (τ : Fin (t + 1))
  /-- the place of channel `z` at time `τ` -/
  | place (z : Ch S (Fin n)) (τ : Fin (t + 1))
  /-- the content of cell `p` of tape `s` -/
  | content (s : S) (p : Fin M)
  deriving DecidableEq, Fintype

/-- `RunVar` as a sum. -/
@[expose] def RunVar.equivSum (S : Type) (n t M : ℕ) :
    RunVar S n t M ≃ Fin t ⊕ Fin (t + 1) ⊕ (Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M) where
  toFun
    | .letter τ => .inl τ
    | .state τ => .inr (.inl τ)
    | .place z τ => .inr (.inr (.inl (z, τ)))
    | .content s p => .inr (.inr (.inr (s, p)))
  invFun
    | .inl τ => .letter τ
    | .inr (.inl τ) => .state τ
    | .inr (.inr (.inl (z, τ))) => .place z τ
    | .inr (.inr (.inr (s, p))) => .content s p
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with _ | _ | ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

omit [DecidableEq S] in
theorem RunVar.card [Fintype S] : Fintype.card (RunVar S n t M) =
    t + (t + 1) + (2 * Fintype.card S + n) * (t + 1) + Fintype.card S * M := by
  rw [Fintype.card_congr (RunVar.equivSum S n t M)]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_congr (chSumEquiv S (Fin n))]
  ring

/-- The values of the variables: letters, states, places and contents. -/
@[reducible, expose] def RunVar.Dom (Γ Q : Type) : RunVar S n t M → Type
  | .letter _ => Letter S (Fin n) Γ
  | .state _ => Q
  | .place _ _ => Fin M
  | .content _ _ => Option Γ

instance [Fintype Γ] [Fintype S] [Fintype Q] : ∀ d : RunVar S n t M, Fintype (d.Dom Γ Q)
  | .letter _ => inferInstanceAs (Fintype (Letter S (Fin n) Γ))
  | .state _ => inferInstanceAs (Fintype Q)
  | .place _ _ => inferInstanceAs (Fintype (Fin M))
  | .content _ _ => inferInstanceAs (Fintype (Option Γ))

instance : ∀ d : RunVar S n t M, DecidableEq (d.Dom Γ Q)
  | .letter _ => inferInstanceAs (DecidableEq (Letter S (Fin n) Γ))
  | .state _ => inferInstanceAs (DecidableEq Q)
  | .place _ _ => inferInstanceAs (DecidableEq (Fin M))
  | .content _ _ => inferInstanceAs (DecidableEq (Option Γ))

/-- An assignment of the hidden variables. -/
abbrev RunAssignment (Γ S Q : Type) (n t M : ℕ) : Type := ∀ d : RunVar S n t M, d.Dom Γ Q

namespace RunAssignment

variable (g : RunAssignment Γ S Q n t M)

/-- The letters. -/
@[expose] def letter (τ : Fin t) : Letter S (Fin n) Γ := g (.letter τ)
/-- The states. -/
@[expose] def state (τ : Fin (t + 1)) : Q := g (.state τ)
/-- The places. -/
@[expose] def place (z : Ch S (Fin n)) (τ : Fin (t + 1)) : Fin M := g (.place z τ)
/-- The contents. -/
@[expose] def content (s : S) (p : Fin M) : Option Γ := g (.content s p)

end RunAssignment

/-- The bits of the clause sum: the code bits of the input, and the one-hot bits of the hidden
variables. -/
abbrev RunBit (Γ S Q : Type) (n t M N : ℕ) : Type :=
  (Fin N × Option Γ) ⊕ Σ d : RunVar S n t M, d.Dom Γ Q

namespace RunBit

/-- The bit "the letter of step `τ` is `a`". -/
@[expose] def letter (τ : Fin t) (a : Letter S (Fin n) Γ) : RunBit Γ S Q n t M N :=
  .inr ⟨.letter τ, a⟩
/-- The bit "the state at time `τ` is `q`". -/
@[expose] def state (τ : Fin (t + 1)) (q : Q) : RunBit Γ S Q n t M N := .inr ⟨.state τ, q⟩
/-- The bit "the place of `z` at time `τ` is `m`". -/
@[expose] def place (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) : RunBit Γ S Q n t M N :=
  .inr ⟨.place z τ, m⟩
/-- The bit "cell `p` of tape `s` holds `y`". -/
@[expose] def content (s : S) (p : Fin M) (y : Option Γ) : RunBit Γ S Q n t M N :=
  .inr ⟨.content s p, y⟩

variable (x : Fin N × Option Γ → Bool) (g : RunAssignment Γ S Q n t M)

@[simp] theorem elim_letter (τ : Fin t) (a : Letter S (Fin n) Γ) :
    Sum.elim x (Pi.oneHot g) (letter τ a) = decide (g.letter τ = a) := rfl
@[simp] theorem elim_state (τ : Fin (t + 1)) (q : Q) :
    Sum.elim x (Pi.oneHot g) (state τ q) = decide (g.state τ = q) := rfl
@[simp] theorem elim_place (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) :
    Sum.elim x (Pi.oneHot g) (place z τ m) = decide (g.place z τ = m) := rfl
@[simp] theorem elim_content (s : S) (p : Fin M) (y : Option Γ) :
    Sum.elim x (Pi.oneHot g) (content s p y) = decide (g.content s p = y) := rfl

end RunBit

/-- The weighted clauses: one for every step, letter and pair of states. -/
structure RunStep (Γ S Q : Type) (n t : ℕ) where
  /-- the step -/
  time : Fin t
  /-- the letter read and written -/
  letter : Letter S (Fin n) Γ
  /-- the state before the step -/
  src : Q
  /-- the state after the step -/
  dst : Q
  deriving DecidableEq, Fintype

/-- `RunStep` as a product. -/
@[expose] def RunStep.equivProd (Γ S Q : Type) (n t : ℕ) :
    RunStep Γ S Q n t ≃ Fin t × Letter S (Fin n) Γ × Q × Q where
  toFun r := (r.time, r.letter, r.src, r.dst)
  invFun := fun (time, letter, src, dst) => ⟨time, letter, src, dst⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq Γ] [DecidableEq S] [DecidableEq Q] in
theorem RunStep.card [Fintype Γ] [Fintype S] [Fintype Q] : Fintype.card (RunStep Γ S Q n t) =
    t * (Fintype.card (Letter S (Fin n) Γ) * (Fintype.card Q * Fintype.card Q)) := by
  rw [Fintype.card_congr (RunStep.equivProd Γ S Q n t)]
  simp [Fintype.card_prod]

/-- The literals of a weighted clause: the letter of the step and the two states. -/
@[expose] def stepLits (r : RunStep Γ S Q n t) : List (RunBit Γ S Q n t M N × Bool) :=
  [(.letter r.time r.letter, true), (.state r.time.castSucc r.src, true),
    (.state r.time.succ r.dst, true)]

/-- The forbidding clauses. -/
inductive RunRule (Γ S : Type) (n t M : ℕ) where
  /-- the first state is the initial one -/
  | initState
  /-- the last state is the final one -/
  | finalState
  /-- a starting channel begins at place `0` -/
  | startPlace (z : Ch S (Fin n))
  /-- the place of `z` advances by what step `τ` emits on `z` -/
  | move (z : Ch S (Fin n)) (τ : Fin t) (m : Fin M) (a : Letter S (Fin n) Γ)
  /-- input `j'` starts one place after the end of input `j` -/
  | nextInput (j j' : Fin n) (m : Fin M)
  /-- a tape write agrees with the content -/
  | readTape (s : S) (b : Bool) (τ : Fin t) (γ : Γ) (m : Fin M)
  /-- the cells beyond the last place of a tape side are blank -/
  | blankTape (s : S) (b : Bool) (m p : Fin M)
  /-- an input read agrees with the code -/
  | readInput (j : Fin n) (τ : Fin t) (γ : Γ) (m : Fin M)
  /-- an input ends with the separator -/
  | endInput (j : Fin n) (m : Fin M)
  deriving DecidableEq

/-- `RunRule` as a sum. -/
@[expose] def RunRule.equivSum (Γ S : Type) (n t M : ℕ) :
    RunRule Γ S n t M ≃ Bool ⊕ Ch S (Fin n) ⊕ (Ch S (Fin n) × Fin t × Fin M × Letter S (Fin n) Γ) ⊕
      (Fin n × Fin n × Fin M) ⊕ (S × Bool × Fin t × Γ × Fin M) ⊕ (S × Bool × Fin M × Fin M) ⊕
      (Fin n × Fin t × Γ × Fin M) ⊕ (Fin n × Fin M) where
  toFun
    | .initState => .inl false
    | .finalState => .inl true
    | .startPlace z => .inr (.inl z)
    | .move z τ m a => .inr (.inr (.inl (z, τ, m, a)))
    | .nextInput j j' m => .inr (.inr (.inr (.inl (j, j', m))))
    | .readTape s b τ γ m => .inr (.inr (.inr (.inr (.inl (s, b, τ, γ, m)))))
    | .blankTape s b m p => .inr (.inr (.inr (.inr (.inr (.inl (s, b, m, p))))))
    | .readInput j τ γ m => .inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, m)))))))
    | .endInput j m => .inr (.inr (.inr (.inr (.inr (.inr (.inr (j, m)))))))
  invFun
    | .inl false => .initState
    | .inl true => .finalState
    | .inr (.inl z) => .startPlace z
    | .inr (.inr (.inl (z, τ, m, a))) => .move z τ m a
    | .inr (.inr (.inr (.inl (j, j', m)))) => .nextInput j j' m
    | .inr (.inr (.inr (.inr (.inl (s, b, τ, γ, m))))) => .readTape s b τ γ m
    | .inr (.inr (.inr (.inr (.inr (.inl (s, b, m, p)))))) => .blankTape s b m p
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, m))))))) => .readInput j τ γ m
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (j, m))))))) => .endInput j m
  left_inv r := by cases r <;> rfl
  right_inv r := by
    rcases r with (_ | _) | _ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _, _⟩ |
      ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> rfl

/-- `deriving Fintype` does not see through `Letter`, so the instance comes from `equivSum`. -/
instance [Fintype Γ] [Fintype S] : Fintype (RunRule Γ S n t M) :=
  Fintype.ofEquiv _ (RunRule.equivSum Γ S n t M).symm

omit [DecidableEq Γ] [DecidableEq S] in
theorem RunRule.card [Fintype Γ] [Fintype S] : Fintype.card (RunRule Γ S n t M) =
    2 + (2 * Fintype.card S + n) + (2 * Fintype.card S + n) * (t * (M * Fintype.card
      (Letter S (Fin n) Γ))) + n * (n * M) + Fintype.card S * (2 * (t * (Fintype.card Γ * M))) +
      Fintype.card S * (2 * (M * M)) + n * (t * (Fintype.card Γ * M)) + n * M := by
  rw [Fintype.card_congr (RunRule.equivSum Γ S n t M)]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_congr (chSumEquiv S (Fin n))]
  ring

/-- The literals of a forbidding clause, for the initial state `i` and the final state `e`. -/
@[expose] def ruleLits (i e : Q) : RunRule Γ S n t M → List (RunBit Γ S Q n t M N × Bool)
  | .initState => [(.state 0 i, false)]
  | .finalState => [(.state (Fin.last t) e, false)]
  | .startPlace z => if h : 0 < M then [(.place z 0 ⟨0, h⟩, false)] else []
  | .move z τ m a => (.place z τ.castSucc m, true) :: (.letter τ a, true) ::
      if h : m.val + (emit [a] z).length < M then [(.place z τ.succ ⟨_, h⟩, false)] else []
  | .nextInput j j' m => (.place (.inp j) (Fin.last t) m, true) ::
      if h : m.val + 1 < M then [(.place (.inp j') 0 ⟨_, h⟩, false)] else []
  | .readTape s b τ γ m =>
      [(.letter τ (some (.tp s b, γ)), true), (.place (.tp s b) τ.castSucc m, true),
        (.content s m (some γ), false)]
  | .blankTape s b m p => [(.place (.tp s b) (Fin.last t) m, true), (.content s p none, false)]
  | .readInput j τ γ m => (.letter τ (some (.inp j, γ)), true) ::
      (.place (.inp j) τ.castSucc m, true) ::
        if h : m.val < N then [(.inl (⟨_, h⟩, some γ), false)] else []
  | .endInput j m => (.place (.inp j) (Fin.last t) m, true) ::
      if h : m.val < N then [(.inl (⟨_, h⟩, none), false)] else []

/-- The forbidding clauses that are in force; the others have weight `1`. -/
@[expose] def RunRule.InForce : RunRule Γ S n t M → Prop
  | .startPlace z => z.start = true
  | .nextInput j j' _ => j'.val = j.val + 1
  | .blankTape _ _ m p => m ≤ p
  | _ => True

instance : DecidablePred (RunRule.InForce (Γ := Γ) (S := S) (n := n) (t := t) (M := M)) := by
  intro r
  cases r <;> unfold RunRule.InForce <;> infer_instance

section Rules

variable (i e : Q) (x : Fin N × Option Γ → Bool) (g : RunAssignment Γ S Q n t M)

/-- No forbidding clause in force has all its literals true. -/
@[expose] def RespectsRules : Prop :=
  ∀ r : RunRule Γ S n t M, r.InForce →
    ¬ ∀ l ∈ ruleLits (N := N) i e r, Sum.elim x (Pi.oneHot g) l.1 = l.2

private theorem good_of_respectsRules (h : RespectsRules i e x g) :
    Good i e x g.letter g.state g.place g.content := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ruleLits, RunRule.InForce] using h .initState trivial
  · simpa [ruleLits, RunRule.InForce] using h .finalState trivial
  · intro z hz
    have hM : 0 < M := (Nat.zero_le _).trans_lt (g.place z 0).isLt
    simpa [ruleLits, hM, Fin.ext_iff] using h (.startPlace z) hz
  · intro z τ
    have := h (.move z τ (g.place z τ.castSucc) (g.letter τ)) trivial
    by_cases hM : (g.place z τ.castSucc).val + (emit [g.letter τ] z).length < M
    · simpa [ruleLits, hM, Fin.ext_iff] using this
    · simp [ruleLits, hM] at this
  · intro j j' hj
    have := h (.nextInput j j' (g.place (.inp j) (Fin.last t))) hj
    by_cases hM : (g.place (.inp j) (Fin.last t)).val + 1 < M
    · simpa [ruleLits, hM, Fin.ext_iff] using this
    · simp [ruleLits, hM] at this
  · intro s b τ γ ho
    simpa [ruleLits, ho] using h (.readTape s b τ γ (g.place (.tp s b) τ.castSucc)) trivial
  · intro s b p hp
    simpa [ruleLits] using h (.blankTape s b (g.place (.tp s b) (Fin.last t)) p) hp
  · intro j τ γ ho
    have := h (.readInput j τ γ (g.place (.inp j) τ.castSucc)) trivial
    by_cases hN : (g.place (.inp j) τ.castSucc).val < N
    · exact ⟨hN, by simpa [ruleLits, ho, hN] using this⟩
    · simp [ruleLits, ho, hN] at this
  · intro j
    have := h (.endInput j (g.place (.inp j) (Fin.last t))) trivial
    by_cases hN : (g.place (.inp j) (Fin.last t)).val < N
    · exact ⟨hN, by simpa [ruleLits, hN] using this⟩
    · simp [ruleLits, hN] at this

private theorem respectsRules_of_good (h : Good i e x g.letter g.state g.place g.content) :
    RespectsRules i e x g := by
  rintro (_ | _ | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ |
    ⟨j, m⟩) hr hl
  · simp [ruleLits, h.first] at hl
  · simp [ruleLits, h.last] at hl
  · have hM : 0 < M := (Nat.zero_le _).trans_lt (g.place z 0).isLt
    exact (by simpa [ruleLits, hM] using hl : _ ≠ _) (Fin.ext (h.zero z hr))
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, RunBit.elim_letter,
      decide_eq_true_eq] at hl
    obtain ⟨rfl, rfl, hl⟩ := hl
    have hs := h.step z τ
    rw [dite_eq_left (hs ▸ (g.place z τ.succ).isLt)] at hl
    exact (by simpa using hl : _ ≠ _) (Fin.ext hs)
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    have hs := h.link j j' hr
    rw [dite_eq_left (hs ▸ (g.place (.inp j') 0).isLt)] at hl
    exact (by simpa using hl : _ ≠ _) (Fin.ext hs)
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, RunBit.elim_letter,
      RunBit.elim_content, decide_eq_true_eq, decide_eq_false_iff_not] at hl
    obtain ⟨ho, rfl, hl, -⟩ := hl
    exact hl (h.write s b τ γ ho)
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, RunBit.elim_content,
      decide_eq_true_eq, decide_eq_false_iff_not] at hl
    obtain ⟨rfl, hl, -⟩ := hl
    exact hl (h.blank s b p hr)
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, RunBit.elim_letter,
      decide_eq_true_eq] at hl
    obtain ⟨ho, rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.read j τ γ ho
    simp [dite_eq_left hN, hx] at hl
  · simp only [ruleLits, List.forall_mem_cons, RunBit.elim_place, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.sep j
    simp [dite_eq_left hN, hx] at hl

/-- **The forbidding clauses check certificates**: an assignment respects the rules in force
exactly when it is a certificate of a run from `i` to `e` on the input with code `x`. -/
theorem respectsRules_iff_good :
    RespectsRules i e x g ↔ Good i e x g.letter g.state g.place g.content :=
  ⟨good_of_respectsRules i e x g, respectsRules_of_good i e x g⟩

end Rules

/-- The literals of all clauses. -/
@[expose] def runLits (i e : Q) :
    RunStep Γ S Q n t ⊕ RunRule Γ S n t M → List (RunBit Γ S Q n t M N × Bool) :=
  Sum.elim stepLits (ruleLits i e)

/-- The weights of all clauses: the matrix entry of a step, and `0` for a rule in force. -/
@[expose] def runWeights (mu : Letter S (Fin n) Γ → Matrix Q Q F) :
    RunStep Γ S Q n t ⊕ RunRule Γ S n t M → F :=
  Sum.elim (fun r => mu r.letter r.src r.dst) fun r => if r.InForce then 0 else 1

/-- **The weighted clauses carry the matrix entries** of the run of the assignment. -/
theorem prod_stepLits [Fintype Γ] [Fintype S] [Fintype Q] (mu : Letter S (Fin n) Γ → Matrix Q Q F)
    (x : Fin N × Option Γ → Bool) (g : RunAssignment Γ S Q n t M) :
    (∏ r : RunStep Γ S Q n t, if ∀ l ∈ stepLits (M := M) (N := N) r,
        Sum.elim x (Pi.oneHot g) l.1 = l.2 then mu r.letter r.src r.dst else 1) =
      ∏ τ, mu (g.letter τ) (g.state τ.castSucc) (g.state τ.succ) := by
  rw [← (RunStep.equivProd Γ S Q n t).symm.prod_comp, Fintype.prod_prod_type]
  refine prod_congr rfl fun τ _ => ?_
  rw [prod_eq_single (g.letter τ, g.state τ.castSucc, g.state τ.succ)]
  · exact ite_eq_left (by simp [stepLits, RunStep.equivProd])
  · rintro ⟨a, q, q'⟩ _ hne
    refine ite_eq_right fun h => hne ?_
    simp only [stepLits, RunStep.equivProd, Equiv.coe_fn_symm_mk, List.forall_mem_cons,
      RunBit.elim_letter, RunBit.elim_state, decide_eq_true_eq] at h
    rw [h.1, h.2.1, h.2.2.1]
  · exact fun h => absurd (mem_univ _) h

open scoped Classical in
/-- **The forbidding clauses select the certificates**: their product is `1` on a certificate and
`0` otherwise. -/
theorem prod_ruleLits [Fintype Γ] [Fintype S] (i e : Q) (x : Fin N × Option Γ → Bool)
    (g : RunAssignment Γ S Q n t M) :
    (∏ r : RunRule Γ S n t M, if ∀ l ∈ ruleLits i e r, Sum.elim x (Pi.oneHot g) l.1 = l.2 then
      (if r.InForce then (0 : F) else 1) else 1) =
        if Good i e x g.letter g.state g.place g.content then 1 else 0 := by
  split_ifs with hg
  · refine prod_eq_one fun r _ => ?_
    by_cases hr : r.InForce
    · exact ite_eq_right ((respectsRules_iff_good i e x g).2 hg r hr)
    · simp [hr]
  · have hh : ¬ RespectsRules i e x g := mt (respectsRules_iff_good i e x g).1 hg
    unfold RespectsRules at hh
    push Not at hh
    obtain ⟨r, hr, hl⟩ := hh
    exact prod_eq_zero (mem_univ r) (by rw [ite_eq_left hl, ite_eq_left hr])

end Cslib.Circuits.Arithmetic.Separation.Tape
