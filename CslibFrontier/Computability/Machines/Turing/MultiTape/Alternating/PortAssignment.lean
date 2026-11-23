/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.PortAssignment
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# A finite alternating machine for local assignment consistency

One fixed finite machine receives the proposed ports, local bits, and raw global assignment on
one work tape. It prepares its universal index choices, checks the length guard, and reads just
one addressed global bit on each branch. Acceptance means that the proposed local word is
exactly the global assignment restricted to the proposed ordered ports.

The native clock includes preparation, universal choices, rewinding, and the deterministic
terminal. Its dependence on the raw global assignment is linear. All polynomial work is confined
to the short context and the binary global length.
-/

public section

namespace Turing.MultiTapeATM.PortAssignment

open MultiTapeTM MultiTapeTM.PortAssignment

private theorem exists_terminal :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (x : Input × List Bool),
        let start := SharedWordFork.start src atm host (encChallenge x) (encChallenge x).length
        let time := C * (x.1.word.length + challengeSize x ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ check x = true) := by
  obtain ⟨d, hd⟩ := exists_check_inO
  obtain ⟨u, S, hS, runner, c, hr⟩ := WorkTapePredicate.exists_of_inO hd
  let terminal := MultiTapeATM.ofTMs (fun _ => runner) (fun _ => false)
  let src : Fin (u + 2) := Fin.natAdd u 0
  let atm := prependTM (TwoWordLoad.rewind src) terminal
  have hsmall : PolyBounded challengeSize (fun x : Input × List Bool =>
      2 * challengeSize x + 3 + c * (challengeSize x ^ d + 1)) :=
    (((PolyBounded.const 2).mul PolyBounded.self).add (.const 3)).add
      ((PolyBounded.const c).mul ((PolyBounded.self.pow d).add (.const 1)))
  obtain ⟨C, D, hbound⟩ := hsmall.exists_le_linear_add_pow
    (fun x => x.1.word.length) (2 + c) (fun x => by simp [challengeSize])
  refine ⟨u + 2, src, _, inferInstance, atm, C, D, ?_⟩
  intro host x start time
  have ht :
      terminal.HaltsWithin (c * (x.1.word.length + challengeSize x ^ d + 1))
        ((WorkTapePredicate.config host (encChallenge x)).withState
          (some terminal.toPTM.initial)) ∧
      (terminal.AcceptsWithin (c * (x.1.word.length + challengeSize x ^ d + 1))
        ((WorkTapePredicate.config host (encChallenge x)).withState
          (some terminal.toPTM.initial)) ↔ check x = true) := by
    rw [MultiTapeATM.haltsWithin_ofTMs_const_iff, MultiTapeATM.acceptsWithin_ofTMs_const_iff]
    rw [show terminal.toPTM.initial = runner.q₀ from rfl, hr]
    simp [WorkTapePredicate.config, Cfg.withState, tapesCfg]
  rw [← SharedWordFork.start_eq_workTape terminal host (encChallenge x)] at ht
  have h := SharedWordFork.rewind_spec src terminal host (encChallenge x)
    (encChallenge x).length _ le_rfl ht.1
  have hclock : (encChallenge x).length + 2 +
      c * (x.1.word.length + challengeSize x ^ d + 1) ≤ time := by
    refine le_trans ?_ (hbound x)
    have hlen := length_encChallenge x
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  exact ⟨h.1.mono hclock, ⟨fun acc => ht.2.mp (h.2.mp (acc.of_halted_stepCoins h.1)),
    fun v => (h.2.mpr (ht.2.mpr v)).mono hclock⟩⟩

/-- A single finite machine verifies every proposed local assignment, with the candidate fixed
before its universal index is chosen. It includes all native preparation and terminal work and
charges the raw global word only linearly, even for repeated or out-of-range ports. -/
theorem exists_evaluator :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : Input),
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * (a.word.length + shortSize a ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          a.context.bits = Cslib.Circuits.Frontier.DescribedNetwork.wordBits
            a.word a.context.ports) := by
  obtain ⟨K, source, S, hS, terminal, A, E, hterminal⟩ := exists_terminal
  obtain ⟨dF, hflags⟩ := exists_flags_inO
  obtain ⟨U, src, Q, hQ, atm, c, hgame⟩ :=
    QuantifiedWord.exists_of_terminal hflags source terminal
  let size := fun a : Input => 2 * shortSize a + (flags a.context).length + 1
  have hflagLength : PolyBounded shortSize (fun a : Input => (flags a.context).length) :=
    flags_polyTime.polyBounded_length.comp (g := Input.context)
      (PolyBounded.self.mono fun a => by simp only [shortSize]; omega)
  have hsize : PolyBounded shortSize size :=
    (((PolyBounded.const 2).mul PolyBounded.self).add hflagLength).add (.const 1)
  let minor := fun a : Input => c * (shortSize a ^ dF + 1) + 8 +
    (4 * shortSize a + 3 + (A * (size a ^ E + 1) + 2 * (flags a.context).length + 1))
  have hminor : PolyBounded shortSize minor :=
    (((PolyBounded.const c).mul ((PolyBounded.self.pow dF).add (.const 1))).add
      (.const 8)).add
      ((((PolyBounded.const 4).mul PolyBounded.self).add (.const 3)).add
        ((((PolyBounded.const A).mul ((hsize.pow E).add (.const 1))).add
          ((PolyBounded.const 2).mul hflagLength)).add (.const 1)))
  obtain ⟨C, D, hbound⟩ := hminor.exists_le_linear_add_pow
    (fun a => a.word.length) (c + 2 + A) (fun a => by simp [shortSize])
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a start time
  let t := A * (a.word.length + size a ^ E + 1)
  have ht (xs : List Bool) (hxs : xs.length = (flags a.context).length) :
      terminal.HaltsWithin t
        (SharedWordFork.start source terminal host (encChallenge (a, xs))
          (encChallenge (a, xs)).length) ∧
      (terminal.AcceptsWithin t
        (SharedWordFork.start source terminal host (encChallenge (a, xs))
          (encChallenge (a, xs)).length) ↔ check (a, xs) = true) := by
    have h := hterminal host (a, xs)
    have hsize' : challengeSize (a, xs) ≤ size a := by
      simp only [challengeSize, encData, length_encPair, encBits_apply, shortSize, size, hxs]
      omega
    have hclock : A * (a.word.length + challengeSize (a, xs) ^ E + 1) ≤ t :=
      Nat.mul_le_mul_left A (by gcongr)
    exact ⟨h.1.mono hclock, ⟨fun acc => h.2.mp (acc.of_halted_stepCoins h.1),
      fun v => (h.2.mpr v).mono hclock⟩⟩
  have h := hgame host a 0 (Nat.zero_le _) t (fun xs => check (a, xs) = true) ht
  simp only [Nat.zero_add] at h
  have hclock : c * (a.word.length + shortSize a ^ dF + 1) + 8 +
      ((frame (encInput a)).length + (t + 2 * (flags a.context).length + 1)) ≤ time := by
    refine le_trans ?_ (hbound a)
    have hlen : (frame (encInput a)).length ≤ 2 * a.word.length + 4 * shortSize a + 3 := by
      simp only [length_frame, encInput_apply, encInputFields, length_encPair,
        encBits_apply, shortSize]
      omega
    dsimp only [minor, t]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  exact ⟨h.1.mono hclock, ⟨fun acc => (plays_check a).mp (h.2.mp (acc.of_halted_stepCoins h.1)),
    fun v => (h.2.mpr ((plays_check a).mpr v)).mono hclock⟩⟩

end Turing.MultiTapeATM.PortAssignment
