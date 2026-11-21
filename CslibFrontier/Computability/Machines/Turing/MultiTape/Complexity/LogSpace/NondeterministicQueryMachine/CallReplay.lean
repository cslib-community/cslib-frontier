/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# Selector replay for same-input calls

A caller forwards the active callee's selectors on the original input. At first halt, one
false selector returns the reply. The parser preserves the unused suffix for subsequent calls.
The call decomposition relates this parser to first-halting replays of the caller.
-/

public section

namespace Turing.NondeterministicQueryMachine

private theorem live_prefix {α : Type} (M : NondeterministicQueryMachine α)
    (input bits : List Bool) (s : α) (hlive : M.halted (M.replay input bits s) = false)
    (n : ℕ) : M.halted (M.replay input (bits.take n) s) = false := by
  cases hp : M.halted (M.replay input (bits.take n) s)
  · rfl
  · have he := M.replay_append input (bits.take n) (bits.drop n) s
    rw [List.take_append_drop, M.replay_of_halted input hp] at he
    rw [he, hp] at hlive
    cases hlive

private theorem split_call {α β : Type} (outer : NondeterministicQueryMachine α)
    (callee : NondeterministicQueryMachine β) (input : List Bool) (wrap : β → α)
    (hwrap : ∀ s, outer.halted (wrap s) = false)
    (hstep : ∀ s bit, callee.halted s = false →
      outer.step input (wrap s) bit = wrap (callee.step input s bit))
    (bits : List Bool) (s : β)
    (hh : outer.halted (outer.replay input bits (wrap s)) = true) :
    ∃ callBits selector rest, bits = callBits ++ selector :: rest ∧
      callee.FirstHalting input callBits s ∧
      outer.replay input callBits (wrap s) = wrap (callee.replay input callBits s) := by
  have hc : callee.halted (callee.replay input bits s) = true := by
    by_contra hn
    have hlive := Bool.eq_false_iff.mpr hn
    rw [outer.replay_map_of_live input callee wrap hstep bits s
      (fun n _ => live_prefix callee input bits s hlive n), hwrap] at hh
    cases hh
  obtain ⟨callBits, ⟨hp, hfirst, _⟩, _⟩ := callee.existsUnique_firstHalting_prefix input hc
  obtain ⟨rest, he⟩ := hp
  have hr := outer.replay_map_of_live input callee wrap hstep callBits s hfirst.2
  cases rest with
  | nil =>
    rw [List.append_nil] at he
    rw [← he, hr, hwrap] at hh
    cases hh
  | cons selector rest =>
    exact ⟨callBits, selector, rest, he.symm, hfirst, hr⟩

private theorem firstHalting_append_live_iff {α : Type} (M : NondeterministicQueryMachine α)
    (input before after : List Bool) (s : α)
    (hlive : M.halted (M.replay input before s) = false) :
    M.FirstHalting input (before ++ after) s ↔
      M.FirstHalting input after (M.replay input before s) := by
  constructor
  · intro h
    refine ⟨by simpa only [M.replay_append] using h.1, fun n hn => ?_⟩
    have hh := h.2 (before.length + n) (by simp only [List.length_append]; omega)
    rw [List.take_append, List.take_of_length_le (by omega : before.length ≤ before.length + n),
      Nat.add_sub_cancel_left, M.replay_append] at hh
    exact hh
  · intro h
    refine ⟨by simpa only [M.replay_append] using h.1, fun n hn => ?_⟩
    by_cases hle : n ≤ before.length
    · rw [List.take_append_of_le_length hle]
      exact live_prefix M input before s hlive n
    · rw [List.take_append, List.take_of_length_le (by omega : before.length ≤ n), M.replay_append]
      exact h.2 (n - before.length) (by simp only [List.length_append] at hn; omega)

/-- Decode a successful callback reply. The callback consumes its first-halting selector prefix
and a false return selector. The unconsumed selector suffix is returned unchanged. -/
@[expose] def readReply {β γ : Type} (callee : NondeterministicQueryMachine β)
    (ret : β → Option γ) (input : List Bool) (s : β) : List Bool → Option (γ × List Bool)
  | [] => none
  | bit :: rest =>
    if callee.halted s then
      if bit then none else (ret s).map fun value => (value, rest)
    else readReply callee ret input (callee.step input s bit) rest

/-- A parsed reply records exactly one first halt followed by a false return selector. -/
theorem readReply_iff {β γ : Type} (callee : NondeterministicQueryMachine β)
    (ret : β → Option γ) (input bits : List Bool) (s : β) (value : γ) (rest : List Bool) :
    readReply callee ret input s bits = some (value, rest) ↔
      ∃ callBits, bits = callBits ++ false :: rest ∧ callee.FirstHalting input callBits s ∧
        ret (callee.replay input callBits s) = some value := by
  induction bits generalizing s with
  | nil => simp [readReply, List.append_eq_nil_iff]
  | cons bit bits ih =>
    cases hhalt : callee.halted s
    · rw [readReply, ite_eq_right (by simp [hhalt]), ih]
      constructor
      · rintro ⟨callBits, rfl, hfirst, hret⟩
        exact ⟨bit :: callBits, rfl,
          (callee.firstHalting_cons_iff input _ _ _).mpr ⟨hhalt, hfirst⟩, hret⟩
      · rintro ⟨(_ | hd) , he, hfirst, hret⟩
        · have hh := hfirst.1
          rw [callee.replay_nil, hhalt] at hh
          cases hh
        · rename_i tl
          change bit :: bits = hd :: (tl ++ false :: rest) at he
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          exact ⟨tl, rfl, ((callee.firstHalting_cons_iff input _ _ _).mp hfirst).2, hret⟩
    · rw [readReply, ite_eq_left hhalt]
      suffices hh : (∃ callBits, bit :: bits = callBits ++ false :: rest ∧
          callee.FirstHalting input callBits s ∧
          ret (callee.replay input callBits s) = some value) ↔
          bit = false ∧ bits = rest ∧ ret s = some value by
        rw [hh]
        cases bit <;> simp [eq_comm, and_comm]
      constructor
      · rintro ⟨(_ | hd), he, hfirst, hret⟩
        · exact ⟨(List.cons.inj he).1, (List.cons.inj he).2, hret⟩
        · have hl := ((callee.firstHalting_cons_iff input _ _ _).mp hfirst).1
          rw [hhalt] at hl
          cases hl
      · rintro ⟨rfl, rfl, hret⟩
        exact ⟨[], rfl, ⟨hhalt, by simp⟩, hret⟩

/-- A successful first halt of a caller suspended at a same-input callback decomposes into
the callback's successful reply and a successful first halt of the resumed caller. -/
theorem successful_call_iff {α β γ : Type}
    (outer : NondeterministicQueryMachine α) (callee : NondeterministicQueryMachine β)
    (input : List Bool) (wrap : β → α) (ret : β → Option γ) (resume : γ → α)
    (reject final : α) (hreject : outer.halted reject = true) (hne : reject ≠ final)
    (hfinal : outer.halted final = true) (hwrap : ∀ s, outer.halted (wrap s) = false)
    (hlive : ∀ s bit, callee.halted s = false →
      outer.step input (wrap s) bit = wrap (callee.step input s bit))
    (hreturn : ∀ s bit, callee.halted s = true →
      outer.step input (wrap s) bit = if bit then reject else (ret s).elim reject resume)
    (s : β) (bits : List Bool) :
    outer.FirstHalting input bits (wrap s) ∧ outer.replay input bits (wrap s) = final ↔
      ∃ value rest, readReply callee ret input s bits = some (value, rest) ∧
        outer.FirstHalting input rest (resume value) ∧
        outer.replay input rest (resume value) = final := by
  have finish (callBits rest : List Bool) (bit : Bool) (h : callee.FirstHalting input callBits s) :
      let t := outer.step input (wrap (callee.replay input callBits s)) bit
      (outer.FirstHalting input (callBits ++ bit :: rest) (wrap s) ∧
        outer.replay input (callBits ++ bit :: rest) (wrap s) = final) ↔
      (outer.FirstHalting input rest t ∧ outer.replay input rest t = final) := by
    have hr := outer.replay_map_of_live input callee wrap hlive callBits s h.2
    have hp := firstHalting_append_live_iff outer input callBits (bit :: rest) (wrap s)
      (by rw [hr, hwrap])
    simp only [hp, outer.replay_append, hr, outer.firstHalting_cons_iff, hwrap, true_and,
      outer.replay_cons]
  constructor
  · rintro ⟨hfirst, hend⟩
    have hh : outer.halted (outer.replay input bits (wrap s)) = true := hend ▸ hfinal
    obtain ⟨callBits, bit, rest, rfl, hc, _⟩ :=
      split_call outer callee input wrap hwrap hlive bits s hh
    have hs := (finish callBits rest bit hc).mp ⟨hfirst, hend⟩
    rw [hreturn _ _ hc.1] at hs
    cases bit
    · simp only [Bool.false_eq_true, ite_false] at hs
      cases he : ret (callee.replay input callBits s) with
      | none =>
        rw [he, Option.elim_none, outer.replay_of_halted input hreject] at hs
        exact (hne hs.2).elim
      | some value =>
        rw [he, Option.elim_some] at hs
        exact ⟨value, rest, (readReply_iff _ _ _ _ _ _ _).mpr ⟨_, rfl, hc, he⟩, hs⟩
    · simp only [ite_true, outer.replay_of_halted input hreject] at hs
      exact (hne hs.2).elim
  · rintro ⟨value, rest, hread, hs⟩
    obtain ⟨callBits, rfl, hc, hret⟩ := (readReply_iff _ _ _ _ _ _ _).mp hread
    apply (finish callBits rest false hc).mpr
    simpa only [hreturn _ _ hc.1, Bool.false_eq_true, ite_false, hret, Option.elim_some] using hs

end Turing.NondeterministicQueryMachine
