/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.AlternatingQueryMachine.Guess
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.AlternatingNative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.AlternatingNative.Resources
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.AlternatingNative.Rounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Tactic.EncLen

/-!
# Compiling alternating query machines into alternating Turing machines

An alternating query machine (`Turing.AlternatingQueryMachine`) whose callbacks are computed within
linear space in the state, started in a state computable within space `O(S)` whose reachable states
have `O(S)` bits, is decided within space `O(S)` by an alternating Turing machine with finitely many
states, provided every branch halts (`Turing.AlternatingQueryMachine.exists_decidesInSpace`). The
abstract state stays on the work tapes and the input is read in place, so `S` may be logarithmic.

The compilation reuses the nondeterministic compiler unchanged
(`Turing.NondeterministicQueryMachine.exists_routines`) on the guessing machine
(`Turing.AlternatingQueryMachine.guess`), whose rounds first guess the player of the state, checking
the guess against `M.universal` and rejecting a wrong one, and then make the move. The alternating
native machine (`Turing.NondeterministicQueryMachine.Native.altMachine`) records the guess in one
bit of finite control and makes the following move universal exactly when the guess was `true`.
An existential guess with one surviving branch followed by a move of the guessed player is a move
of the player of the state, so the native machine accepts exactly when the alternating query
machine does, by induction on the labelling (`Turing.AlternatingQueryMachine.AcceptsFrom`) one way
and on the number of moves (`Turing.MultiTapeATM.AcceptsWithin`) the other.

This is the compiler step of the inclusion `DTIME(2 ^ O(s)) ⊆ ASPACE(s)`
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981].

## Main results

* `Turing.AlternatingQueryMachine.exists_decidesInSpace`: the compiler, for deciders.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

public section

namespace Turing.AlternatingQueryMachine

open MultiTapeTM ComputableInSpace NondeterministicQueryMachine

variable {α σ : Type} {enc : α ↪ List Bool} {encS : σ ↪ List Bool}

/-- The guessing machine accepts, through the alternating native machine, exactly the states from
which `M` accepts. -/
private theorem acceptsFrom_iff_exists_acceptsWithin (M : AlternatingQueryMachine σ)
    {start : α → σ × Option Bool} {S : α → ℕ} (R : Routines M.guess start enc S) (a : α)
    (s : σ) (hr : (M.guess.withInit (start a)).Reachable (enc a) (s, none)) :
    M.AcceptsFrom (enc a) s ↔ ∃ n, R.atm.AcceptsWithin n (R.boundaryCfg a (s, none) none) := by
  have hlive {s : σ} (hh : M.halted s = false) {p : Option Bool} (hp : p ≠ some false) :
      M.guess.halted (s, p) = false := by
    rcases p with _ | ⟨_ | _⟩ <;> simp_all [guess]
  have hround := R.exists_acceptsWithin_boundaryCfg_of_live a
  constructor
  · intro h
    induction h with
    | @halt s hh ha =>
      obtain ⟨τ, hτ⟩ :=
        R.exists_acceptsWithin_boundaryCfg_of_halted a _ hr (by simp [guess, hh]) none
      exact ⟨τ, (hτ τ).mpr ⟨le_rfl, by simpa [guess] using ha⟩⟩
    | @existsChoice s b hh hu _ ih =>
      have hstep₁ : M.guess.step (enc a) (s, none) false = (s, some true) := by
        simp [M.guess_step_none (enc a) hh, hu]
      have hr₁ := hstep₁ ▸ hr.step _ (enc a) false
      have hstep₂ := M.guess_step_some_true (enc a) hh b
      obtain ⟨n, hn⟩ := ih (hstep₂ ▸ hr₁.step _ (enc a) b)
      obtain ⟨τ, hτ⟩ := hround _ hr (hlive hh (by simp)) none
      obtain ⟨τ₁, hτ₁⟩ := hround _ hr₁ (hlive hh (by simp)) (some false)
      refine ⟨n + τ₁ b + 1 + τ false + 1, ?_⟩
      rw [hτ, ite_eq_right (by simp)]
      refine ⟨false, by omega, ?_⟩
      rw [hstep₁, show Native.nextGuess none false = some false from rfl,
        Nat.add_sub_cancel, hτ₁, ite_eq_right (by simp)]
      refine ⟨b, by omega, ?_⟩
      simpa only [hstep₂, show Native.nextGuess (some false) b = none from rfl,
        Nat.add_sub_cancel] using hn
    | @forallChoice s hh hu _ ih =>
      have hstep₁ : M.guess.step (enc a) (s, none) true = (s, some true) := by
        simp [M.guess_step_none (enc a) hh, hu]
      have hr₁ := hstep₁ ▸ hr.step _ (enc a) true
      have hstep₂ := M.guess_step_some_true (enc a) hh
      choose n hn using fun b => ih b (hstep₂ b ▸ hr₁.step _ (enc a) b)
      obtain ⟨τ, hτ⟩ := hround _ hr (hlive hh (by simp)) none
      obtain ⟨τ₁, hτ₁⟩ := hround _ hr₁ (hlive hh (by simp)) (some true)
      let N := max (n false + τ₁ false) (n true + τ₁ true)
      have hle (b : Bool) : n b + τ₁ b ≤ N := b.rec (le_max_left _ _) (le_max_right _ _)
      refine ⟨N + 1 + τ true + 1, ?_⟩
      rw [hτ, ite_eq_right (by simp)]
      refine ⟨true, by omega, ?_⟩
      rw [hstep₁, show Native.nextGuess none true = some true from rfl,
        Nat.add_sub_cancel, hτ₁, ite_eq_left rfl]
      refine fun b => ⟨by have := hle b; omega, ?_⟩
      rw [hstep₂ b, show Native.nextGuess (some true) b = none from rfl]
      exact (hn b).mono (by have := hle b; omega)
  · rintro ⟨n, hn⟩
    induction n using Nat.strong_induction_on generalizing s with | _ n ih => ?_
    cases hh : M.halted s with
    | true =>
      obtain ⟨τ, hτ⟩ :=
        R.exists_acceptsWithin_boundaryCfg_of_halted a _ hr (by simp [guess, hh]) none
      exact .halt hh (by simpa [guess] using ((hτ n).mp hn).2)
    | false =>
      rcases n with _ | m
      · exact absurd hn (MultiTapeATM.not_acceptsWithin_zero _ rfl)
      obtain ⟨τ, hτ⟩ := hround _ hr (hlive hh (by simp)) none
      rw [hτ, ite_eq_right (by simp)] at hn
      obtain ⟨g, _, hn⟩ := hn
      have hr₁ := M.guess_step_none (enc a) hh g ▸ hr.step _ (enc a) g
      rw [M.guess_step_none (enc a) hh] at hn
      cases hgu : (g == M.universal s) with
      | false =>
        rw [hgu] at hn hr₁
        obtain ⟨τ', hτ'⟩ := R.exists_acceptsWithin_boundaryCfg_of_halted a _ hr₁ (by simp [guess]) _
        exact absurd ((hτ' _).mp hn).2 Bool.false_ne_true
      | true =>
        rw [hgu] at hn hr₁
        obtain ⟨τ₁, hτ₁⟩ := hround _ hr₁ (hlive hh (by simp)) (Native.nextGuess none g)
        rcases hm' : m - τ g with _ | m'
        · exact absurd (hm' ▸ hn) (MultiTapeATM.not_acceptsWithin_zero _ rfl)
        rw [hm', hτ₁] at hn
        have hr₂ (b : Bool) := M.guess_step_some_true (enc a) hh b ▸ hr₁.step _ (enc a) b
        cases g
        · rw [show Native.nextGuess none false = some false from rfl, ite_eq_right (by simp)] at hn
          obtain ⟨b, _, hn⟩ := hn
          rw [M.guess_step_some_true (enc a) hh b] at hn
          exact .existsChoice b hh (beq_iff_eq.mp hgu).symm (ih _ (by omega) _ (hr₂ b) hn)
        · rw [show Native.nextGuess none true = some true from rfl, ite_eq_left rfl] at hn
          refine .forallChoice hh (beq_iff_eq.mp hgu).symm fun b => ?_
          have hnb := (hn b).2
          rw [M.guess_step_some_true (enc a) hh b] at hnb
          exact ih _ (by omega) _ (hr₂ b) hnb

/-- **Compiling alternating query machines into alternating Turing machines.** Let `M` be an
alternating query machine whose callbacks (query, step, halting, acceptance and player) are
computed within linear space in the state, started on the input `enc a` in a state `start a`
computable within space `S a ≥ log₂ |enc a| + 1`. If every state reached from `start a` has at most
`c * S a` bits and every branch from `start a` halts within `time a` steps, then some alternating
Turing machine with a binary alphabet and finitely many states decides, within space `O(S)` and
with every branch halting, the problem of whether `M` accepts from `start a`
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981]. The abstract state is
kept on the work tapes, never in finite control, and the input is read in place; the bound `time`
is used only in the proof. -/
theorem exists_decidesInSpace (M : AlternatingQueryMachine σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next (encPair encS NondeterministicQueryMachine.encReadChoice) encS
      fun p => (encPair encS NondeterministicQueryMachine.encReadChoice p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    (huniversal : ComputableInSpace M.universal encS encBool fun s => (encS s).length)
    (start : α → σ) (time : α → ℕ)
    (hhalt : ∀ a (choices : List Bool), time a ≤ choices.length →
      M.halted (M.replay (enc a) choices (start a)) = true)
    {A : Set α} (hcorrect : ∀ a, a ∈ A ↔ M.AcceptsFrom (enc a) (start a))
    (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hstart : ComputableInSpace start enc encS S)
    (hsize : ∃ c, ∀ a (choices : List Bool),
      (encS (M.replay (enc a) choices (start a))).length ≤ c * S a) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State) (c : ℕ),
      atm.DecidesInSpace enc A fun a => c * S a := by
  obtain ⟨c, hc⟩ := hsize
  have hS (a : α) : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  let start' : α → σ × Option Bool := fun a => (start a, none)
  have hsize' : ∃ c', ∀ a (choices : List Bool),
      (encGuessState encS ((M.guess.withInit (start' a)).run (enc a) choices)).length ≤
        c' * S a := ⟨2 * c + 6, fun a choices => by
    obtain ⟨choices', p', h⟩ := M.guess_replay (enc a) choices (start a) none
    have hp : (encOption encBool p').length ≤ 4 := by
      cases p' <;> simp [encOption_none, encOption_some, encBool_apply]
    rw [run_withInit, h]
    simp only [encGuessState, length_encPair]
    nlinarith [hc a choices', hS a]⟩
  obtain ⟨R⟩ := M.guess.exists_routines (M.guess_query_inSpace hquery)
    (M.guess_next_inSpace hnext huniversal) (M.guess_halted_inSpace hhalted)
    (M.guess_accept_inSpace haccept) start' S hlog (budget_prod hstart (budget_const none)) hsize'
  let : Finite R.SI := R.finiteI
  let : ∀ b, Finite (R.SP b) := R.finiteP
  let : Finite R.SF := R.finiteF
  refine ⟨R.k, Native.State R.SI R.SP R.SF × Option Bool, inferInstance, R.atm,
    R.k * (2 * R.c + 1), fun a => ⟨(R.runsInSpace_atm a).mono ?_, ?_⟩,
    fun a => R.exists_runsInTime_atm a (time := 2 * time a) fun choices hlen => ?_⟩
  · calc R.k * (2 * (R.c * S a) + 1) ≤ R.k * ((2 * R.c + 1) * S a) :=
          Nat.mul_le_mul_left _ (by nlinarith only [hS a])
      _ = R.k * (2 * R.c + 1) * S a := by ring
  · rw [hcorrect a, R.accepts_atm_iff a]
    exact acceptsFrom_iff_exists_acceptsWithin M R a (start a)
      ((M.guess.withInit (start' a)).reachable_init (enc a))
  · rw [run_withInit]
    exact M.guess_halted_replay (hhalt a) choices hlen.ge

end Turing.AlternatingQueryMachine
