/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp

/-!
# Loops that read their input, within space

`Turing.MultiTapeTM.ComputableInSpace` does not charge the read-only input, but the loops of
`Turing.MultiTapeTM.ComputableInSpace.iterate` and
`Turing.MultiTapeTM.ComputableInSpace.iterateUntil` take a step function of the state alone, so a
round cannot look at the input. The loop of this module can: a round reads the input bit at a
position computed from the state (`Turing.MultiTapeTM.queryRound`), and the loop runs until a test
on the state holds. It is computable within the space of the start state and of the states it
passes through, plus the logarithm of the length of the input for the position counter of the
underlying query machine (`Turing.QueryMachine.computableInSpaceFrom`), which the caller no longer
declares.

The rule comes in two forms. `queryLoop` asks for the number of rounds and a bound on the iterates,
which suits loops with a closed form. `queryLoop_of_invariant` asks for an invariant of the states
indexed by a variant that decreases in every round, in the style of a total-correctness rule: the
invariant bounds the states and determines the result at the first state where the test holds.

The result is the final state and is charged to the budget, so the rule composes with the other
budget rules of `ComputableInSpace` and with the `space` tactic. A budget logarithmic in the length
of the input gives logarithmic space (`Turing.MultiTapeTM.ComputableInSpace.computableInLogSpace`).

## Main definitions

* `Turing.MultiTapeTM.queryRound`: a round that reads one input bit.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.queryLoop`: iterating a round that reads the input until a
  test holds, within the space of the states plus the logarithm of the length of the input.
* `Turing.MultiTapeTM.ComputableInSpace.queryLoop_of_invariant`: the same from an invariant with a
  decreasing variant, which gives termination, the bound on the states and the result.
* `Turing.MultiTapeTM.ComputableInSpace.computableInLogSpace`: a logarithmic budget gives
  logarithmic space.
-/

public section

namespace Turing.MultiTapeTM

variable {α β σ : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {encS : σ ↪ List Bool}

/-- A round of a loop that reads its input `w`: read the bit at position `query s`, `none` past the
end of `w`, and move to `next`. -/
@[expose] def queryRound (query : σ → ℕ) (next : σ × Option Bool → σ) (w : List Bool) (s : σ) : σ :=
  next (s, w[query s]?)

namespace ComputableInSpace

/-- A budget logarithmic in the length of the encoded input gives logarithmic space: the same
machine, without the bound on the length of the value. -/
theorem computableInLogSpace {f : α → β}
    (h : ComputableInSpace f enc encB fun a => Nat.log2 (enc a).length) :
    ComputableInLogSpace f enc encB :=
  let ⟨t, c, h, _⟩ := h
  ⟨t, c, h⟩

/-- The query machine of a loop: its rounds are the steps, it halts at the test, emits nothing
before, and then emits the encoded state. -/
private def loopMachine (encS : σ ↪ List Bool) (init : σ) (query : σ → ℕ)
    (next : σ × Option Bool → σ) (done : σ → Bool) : QueryMachine σ where
  init := init
  query := query
  next := next
  emit _ := []
  halted := done
  finish s := encS s

/-- Before the test holds, the steps of the query machine are the rounds of the loop. -/
private theorem runFrom_loopMachine {init : σ} {query : σ → ℕ} {next : σ × Option Bool → σ}
    {done : σ → Bool} (w : List Bool) (s : σ) {n : ℕ}
    (hlt : ∀ j < n, done ((queryRound query next w)^[j] s) = false) :
    (loopMachine encS init query next done).runFrom w s n = (queryRound query next w)^[n] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [QueryMachine.runFrom_succ, ih fun j hj => hlt j (by omega), Function.iterate_succ_apply',
      QueryMachine.step]
    simp only [loopMachine, hlt n (by omega), Bool.false_eq_true, ↓reduceIte, QueryMachine.read,
      queryRound]

/-- **Iterating a round that reads the input until a test holds.** From the state `start a`, a
round reads the input bit at the position `query s` and moves to `next`, until `done`. If the
start state is computable within the budget `S`, the parts of a round within space linear in the
encoded state, and the states of the loop have encodings of length `O(S + log n)` for inputs of
length `n`, then the final state is computable within space `O(S + log n)`. The number of rounds
`n a`, the first at which the test holds, need not be computable, and the input is not charged. -/
theorem queryLoop {start : α → σ} {query : σ → ℕ} {next : σ × Option Bool → σ} {done : σ → Bool}
    {n S : α → ℕ} (hstart : ComputableInSpace start enc encS S)
    (hquery : ComputableInSpace query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace next (QueryMachine.encStateRead encS) encS
      fun p => (QueryMachine.encStateRead encS p).length)
    (hdone : ComputableInSpace done encS encBool fun s => (encS s).length)
    (hn : ∀ a, done ((queryRound query next (enc a))^[n a] (start a)) = true)
    (hlt : ∀ a, ∀ j < n a, done ((queryRound query next (enc a))^[j] (start a)) = false)
    (hsize : ∃ c, ∀ a, ∀ j ≤ n a, (encS ((queryRound query next (enc a))^[j] (start a))).length ≤
      c * (S a + Nat.log2 (enc a).length + 1)) :
    ComputableInSpace (fun a => (queryRound query next (enc a))^[n a] (start a)) enc encS
      fun a => S a + Nat.log2 (enc a).length := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · exact (hstart.of_enc_eq fun a => isEmptyElim a).mono_le fun a => isEmptyElim a
  obtain ⟨c, hc⟩ := hsize
  let M := loopMachine encS (start a₀) query next done
  have hrun (a : α) {j : ℕ} (hj : j ≤ n a) :
      M.runFrom (enc a) (start a) j = (queryRound query next (enc a))^[j] (start a) :=
    runFrom_loopMachine (enc a) (start a) fun i hi => hlt a i (by omega)
  obtain ⟨t, d, h⟩ := M.computableInSpaceFrom (enc := enc) (encOut := encS)
    (f := fun a => (queryRound query next (enc a))^[n a] (start a)) hquery hnext
    (budget_const ([] : List Bool)) hdone
    ((budget_id (.refl _)).of_enc_eq fun _ => rfl) n
    (fun a => S a + Nat.log2 (enc a).length + 1)
    (hstart.mono_le fun a => by omega)
    (fun a => by rw [hrun a le_rfl]; exact hn a)
    (fun a j hj => by rw [hrun a hj.le]; exact hlt a j hj)
    (fun a => by
      rw [QueryMachine.outputFrom_eq_finish_of_emit_nil _ _ (fun _ => rfl), hrun a le_rfl]; rfl)
    (fun a => by omega)
    ⟨c, fun a j hj => by rw [hrun a hj]; exact hc a j hj⟩
  exact ⟨t, max d c, h.mono (fun _ => le_rfl) fun a => Nat.mul_le_mul_right _ (le_max_left d c),
    fun a => (hc a (n a) le_rfl).trans (Nat.mul_le_mul_right _ (le_max_right d c))⟩

/-- **A loop that reads the input, from an invariant with a variant.** As
`Turing.MultiTapeTM.ComputableInSpace.queryLoop`, with the number of rounds and the bound on the
iterates replaced by an invariant `Inv a m s` of the states `s` on the input `a`, indexed by a
variant `m`: it holds at the start, a round from a state where the test fails keeps it with a
smaller variant, it bounds the encoded state by `O(S + log n)`, and where the test holds it
determines the state as `f a`. Then `f` is computable within space `O(S + log n)`. -/
theorem queryLoop_of_invariant {start : α → σ} {query : σ → ℕ} {next : σ × Option Bool → σ}
    {done : σ → Bool} {S : α → ℕ} {f : α → σ} (Inv : α → ℕ → σ → Prop)
    (hstart : ComputableInSpace start enc encS S)
    (hquery : ComputableInSpace query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace next (QueryMachine.encStateRead encS) encS
      fun p => (QueryMachine.encStateRead encS p).length)
    (hdone : ComputableInSpace done encS encBool fun s => (encS s).length)
    (hinit : ∀ a, ∃ m, Inv a m (start a))
    (hround : ∀ a m s, Inv a m s → done s = false →
      ∃ m' < m, Inv a m' (queryRound query next (enc a) s))
    (hf : ∀ a m s, Inv a m s → done s = true → s = f a)
    (hsize : ∃ c, ∀ a m s, Inv a m s → (encS s).length ≤ c * (S a + Nat.log2 (enc a).length + 1)) :
    ComputableInSpace f enc encS fun a => S a + Nat.log2 (enc a).length := by
  -- from a state satisfying the invariant, the test holds after at most the variant many rounds
  have hhalt (a : α) (m : ℕ) : ∀ s, Inv a m s →
      ∃ N, done ((queryRound query next (enc a))^[N] s) = true := by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro s hs
      cases hd : done s with
      | true => exact ⟨0, hd⟩
      | false =>
        obtain ⟨m', hm', hs'⟩ := hround a m s hs hd
        obtain ⟨N, hN⟩ := ih m' hm' _ hs'
        exact ⟨N + 1, by rwa [Function.iterate_succ_apply]⟩
  have hex (a : α) : ∃ N, done ((queryRound query next (enc a))^[N] (start a)) = true :=
    let ⟨m, hm⟩ := hinit a
    hhalt a m _ hm
  classical
  have hlt (a : α) (j : ℕ) (hj : j < Nat.find (hex a)) :
      done ((queryRound query next (enc a))^[j] (start a)) = false :=
    Bool.eq_false_iff.mpr (Nat.find_min (hex a) hj)
  -- the invariant holds up to the first round at which the test holds
  have hinv (a : α) : ∀ j ≤ Nat.find (hex a),
      ∃ m, Inv a m ((queryRound query next (enc a))^[j] (start a)) := by
    intro j hj
    induction j with
    | zero => exact hinit a
    | succ j ih =>
      obtain ⟨m, hm⟩ := ih (by omega)
      obtain ⟨m', -, hm'⟩ := hround a m _ hm (hlt a j (by omega))
      exact ⟨m', by rwa [Function.iterate_succ_apply']⟩
  obtain ⟨c, hc⟩ := hsize
  refine (queryLoop (n := fun a => Nat.find (hex a)) hstart hquery hnext hdone
    (fun a => Nat.find_spec (hex a)) hlt ⟨c, fun a j hj => ?_⟩).of_enc_eq fun a => ?_
  · obtain ⟨m, hm⟩ := hinv a j hj
    exact hc a m _ hm
  · obtain ⟨m, hm⟩ := hinv a _ le_rfl
    rw [hf a m _ hm (Nat.find_spec (hex a))]

end ComputableInSpace

end Turing.MultiTapeTM
