/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Union
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Closure properties of nondeterministic logarithmic space

`NL` is closed under logspace many-one reductions, for arbitrary encodings of the instances
(`Cslib.Complexity.LogSpaceReducible.mem_NL`). This is the nondeterministic analogue of the
closure of `L` [Sipser, Theorem 8.23][Sipser2013], proved by the same recomputation: if `A`
reduces to `B ∈ NL` by a function `f` computable in logarithmic space, a nondeterministic machine
for `A` simulates the machine for `B` on `f a` without writing `f a` down, recomputing each symbol
of it that the simulated machine reads. `NL` is also closed under union
(`Cslib.Complexity.union_mem_NL`), by guessing which machine to run, and so, being closed under
complement by the Immerman–Szelepcsényi theorem, under intersection
(`Cslib.Complexity.inter_mem_NL`).

Both constructions run the machine of a problem in `NL` through the universal recognizer within a
budget (`Turing.MultiTapeTM.Universal.budgetedNUniversal`), a nondeterministic query machine whose
state holds the configuration of the simulated machine. Its budget is a constant times
`log₂ n + 1` for inputs of length `n`, which bounds the configurations of the simulated machine on
`f a`, since `f a` has polynomial length. The recomputation is
`Turing.NondeterministicQueryMachine.recompute`, the union
`Turing.NondeterministicQueryMachine.union`, and the native compiler of query machines turns them
into nondeterministic machines within logarithmic space; these recognize their problems, and
`Cslib.Complexity.mem_NL_of_recognizesInSpace` makes every branch halt.

## Main results

* `Cslib.Complexity.LogSpaceReducible.mem_NL`: `NL` is closed under logspace reductions.
* `Cslib.Complexity.LogSpaceHard.subset_NL`: a hard problem in `NL` places its class in `NL`.
* `Cslib.Complexity.union_mem_NL`, `Cslib.Complexity.inter_mem_NL`: `NL` is closed under union and
  intersection.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.23][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal
  _root_.Turing.NondeterministicQueryMachine ComputableInSpace

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A A' : Set α} {B : Set β}

/-- The budget `(log₂ n + 1) * K` in unary, within space `log₂ n + 1`, where `n` is the length of
`enc a`. -/
private theorem budget_inSpace (K : ℕ) :
    ComputableInSpace (fun a => (Nat.log2 (enc a).length + 1) * K) enc encUnary
      fun a => Nat.log2 (enc a).length + 1 := by
  have hlen : ComputableInLogSpace (fun a => (enc a).length) enc encUnary :=
    ComputableInLogSpace.bitsLength.comp
      (ComputableInLogSpace.of_eq (f := fun a => enc a) (encMid := encBits) fun _ => by
        simp [encBits_apply])
  obtain ⟨t, c, h⟩ := ComputableInLogSpace.unaryMulConst K
    (ComputableInLogSpace.unaryAdd (ComputableInLogSpace.unaryLog2 hlen)
      (ComputableInLogSpace.const 1))
  refine ⟨t, c + K, h.mono (fun _ => le_rfl) fun a => ?_, fun a => ?_⟩
  · exact Nat.mul_le_mul (Nat.le_add_right c K) (Nat.le_succ _)
  · simp only [encUnary_apply, List.length_replicate]
    nlinarith

/-- **A problem in `NL`, read through a logspace function, as the universal recognizer.** For
`B ∈ NL` and `f` computable in logarithmic space, the universal recognizer within a budget of
`O(log n)` bits on inputs `enc a` of length `n`, started on the description of a machine for `B`,
accepts `encB (f a)` exactly when `f a ∈ B`, and its states take space `O(log n)`. -/
private theorem exists_nuStart (hB : B ∈ NL encB) {f : α → β}
    (hf : ComputableInLogSpace f enc encB) :
    ∃ start : α → NUState,
      ComputableInSpace start enc eNU (fun a => Nat.log2 (enc a).length + 1) ∧
      (∃ C, ∀ a choices,
        (eNU ((budgetedNUniversal.withInit (start a)).run (encB (f a)) choices)).length ≤
          C * (Nat.log2 (enc a).length + 1)) ∧
      ∀ a, f a ∈ B ↔ (budgetedNUniversal.withInit (start a)).Accepts (encB (f a)) := by
  obtain ⟨k, State, _, ntm, c, hdec, -⟩ := hB
  obtain ⟨eS, heS⟩ := Countable.exists_injective_nat State
  set D := descN ⟨eS, heS⟩ eBit ntm
  obtain ⟨C, d, hlen⟩ := hf.polyBounded_length.exists_le
  set K₂ := Nat.size (C + 1) + 2 * d + 1
  set K := 2 * descLen D + 4 + k + (2 + 6 * (2 * descLen D + 5) * c) * K₂
  have hbud (a : α) : cfgSpaceBound (descLen D) (encB (f a)).length k
      (c * (Nat.log2 (encB (f a)).length + 1)) ≤ (Nat.log2 (enc a).length + 1) * K := by
    have hp : 1 ≤ ((enc a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hL : (encNat ((encB (f a)).length + 1)).length ≤ K₂ * (Nat.log2 (enc a).length + 1) :=
      length_encNat_le_of_le_mul_pow (by nlinarith [hlen a])
    have hS := (log2_succ_le_length_encNat (encB (f a)).length).trans hL
    have h1 : 1 ≤ Nat.log2 (enc a).length + 1 := Nat.le_add_left _ _
    simp only [cfgSpaceBound]
    generalize Nat.log2 (enc a).length + 1 = ℓ at *
    generalize Nat.log2 (encB (f a)).length + 1 = m at *
    generalize (encNat ((encB (f a)).length + 1)).length = L at *
    have hcS : c * m ≤ c * (K₂ * ℓ) := Nat.mul_le_mul_left c hS
    have e : ℓ * (2 * descLen D + 4 + k + (2 + 6 * (2 * descLen D + 5) * c) * K₂) =
        (2 * descLen D + 4 + k) * ℓ + 2 * (K₂ * ℓ) + 6 * (2 * descLen D + 5) * (c * (K₂ * ℓ)) := by
      ring
    have hc6 : 3 * (2 * descLen D + 5) * 2 * (c * m) ≤
        6 * (2 * descLen D + 5) * (c * (K₂ * ℓ)) := by
      have := Nat.mul_le_mul_left (6 * (2 * descLen D + 5)) hcS
      linarith
    have hk : 2 * descLen D + 4 + k ≤ (2 * descLen D + 4 + k) * ℓ := Nat.le_mul_of_pos_right _ h1
    rw [e]
    omega
  refine ⟨fun a => nuStart D ((Nat.log2 (enc a).length + 1) * K),
    nuStart_budget (budget_const D) (budget_inSpace K),
    ⟨40 * descLen D + 4 * K + 40, fun a choices => ?_⟩, fun a => ?_⟩
  · refine (length_eNU_run_le _ _ _ choices).trans ?_
    have h1 : 1 ≤ Nat.log2 (enc a).length + 1 := Nat.le_add_left _ _
    generalize Nat.log2 (enc a).length + 1 = ℓ at *
    nlinarith
  · rw [budgetedNUniversal_accepts_iff, ← accepts_iff_bAccepts_descN _ ntm (hdec (f a)).1 (hbud a)]
    exact (hdec (f a)).2

/-- **`NL` is closed under logspace reductions**, for arbitrary encodings of the instances of both
problems: a nondeterministic machine for `A` runs the machine for `B` on the image of its input,
recomputing each symbol of the image that this machine reads, within logarithmic space. This is the
nondeterministic analogue of [Sipser, Theorem 8.23][Sipser2013], with the same recomputation. -/
theorem LogSpaceReducible.mem_NL (hAB : LogSpaceReducible enc encB A B) (hB : B ∈ NL encB) :
    A ∈ NL enc := by
  obtain ⟨f, hf, hA⟩ := hAB
  obtain ⟨start, hstart, hsize, hcorrect⟩ := exists_nuStart hB hf
  obtain ⟨k, State, _, ntm, c, hrec⟩ := exists_recognizesInSpace_recompute budgetedNUniversal
    budgetedNUniversal_query_inSpace budgetedNUniversal_next_inSpace
    budgetedNUniversal_halted_inSpace budgetedNUniversal_accept_inSpace hf start _
    (fun _ => le_rfl) hstart hsize
  have hset : {a | (budgetedNUniversal.withInit (start a)).Accepts (encB (f a))} = A :=
    Set.ext fun a => ((hA a).trans (hcorrect a)).symm
  exact mem_NL_of_recognizesInSpace (hset ▸ hrec)

/-- **A problem hard for a class under logspace reductions and in `NL` places the class in
`NL`**, for every encoding of instances. -/
theorem LogSpaceHard.subset_NL {D : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    (hB : LogSpaceHard D encB B) (hNL : B ∈ NL encB) (enc : α ↪ List Bool) : D enc ⊆ NL enc :=
  fun _ hA => (hB enc _ hA).mem_NL hNL

/-- **`NL` is closed under union**: guess which of the two machines to run. -/
theorem union_mem_NL (hA : A ∈ NL enc) (hA' : A' ∈ NL enc) : A ∪ A' ∈ NL enc := by
  obtain ⟨s, hs, ⟨cs, hcs⟩, hcorrect⟩ := exists_nuStart hA ComputableInLogSpace.id
  obtain ⟨s', hs', ⟨cs', hcs'⟩, hcorrect'⟩ := exists_nuStart hA' ComputableInLogSpace.id
  have hsize : ∃ C, ∀ a choices, (eUnion NUState NUState eNU eNU
      (((union budgetedNUniversal budgetedNUniversal).withInit ⟨s a, s' a, none⟩).run (enc a)
        choices)).length ≤ C * (Nat.log2 (enc a).length + 1) := by
    refine ⟨2 * cs + 2 * cs' + 8, fun a choices => (length_eUnion_le _).trans ?_⟩
    have h1 : 1 ≤ Nat.log2 (enc a).length + 1 := Nat.le_add_left _ _
    rw [run_withInit]
    rcases choices with _ | ⟨_ | _, choices⟩
    · have h₁ := hcs a []
      have h₂ := hcs' a []
      simp only [run_withInit, replay_nil] at h₁ h₂ ⊢
      nlinarith
    · have h₁ := hcs a choices
      have h₂ := hcs' a []
      simp only [run_withInit, replay_nil] at h₁ h₂
      rw [replay_cons, step_union_none, replay_union_left]
      nlinarith
    · have h₁ := hcs a []
      have h₂ := hcs' a choices
      simp only [run_withInit, replay_nil] at h₁ h₂
      rw [replay_cons, step_union_none, replay_union_right]
      nlinarith
  obtain ⟨k, State, _, ntm, c, hrec⟩ := exists_recognizesInSpace (enc := enc)
    (union budgetedNUniversal budgetedNUniversal)
    (union_query_inSpace budgetedNUniversal_query_inSpace budgetedNUniversal_query_inSpace)
    (union_next_inSpace budgetedNUniversal_next_inSpace budgetedNUniversal_next_inSpace)
    (union_halted_inSpace budgetedNUniversal_halted_inSpace budgetedNUniversal_halted_inSpace)
    (union_accept_inSpace budgetedNUniversal_accept_inSpace budgetedNUniversal_accept_inSpace)
    (fun a => ⟨s a, s' a, none⟩) (A := A ∪ A')
    (fun a => by rw [union_accepts_iff, Set.mem_union, hcorrect, hcorrect']) _ (fun _ => le_rfl)
    (eUnion_mk_budget _ _ _ _ hs hs' (budget_const none)) hsize
  exact mem_NL_of_recognizesInSpace hrec

/-- **`NL` is closed under intersection**: by De Morgan, from closure under union and, by the
Immerman–Szelepcsényi theorem, under complement. -/
theorem inter_mem_NL (hA : A ∈ NL enc) (hA' : A' ∈ NL enc) : A ∩ A' ∈ NL enc := by
  rw [← compl_compl (A ∩ A'), Set.compl_inter]
  exact compl_mem_NL (union_mem_NL (compl_mem_NL hA) (compl_mem_NL hA'))

end Cslib.Complexity
