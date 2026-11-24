/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.ScalarInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordPredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# A finite native machine for scalar coefficient bits

The request is on a work tape and the read-only host input is arbitrary. One finite machine and
one polynomial clock work for every signed integer, binary shift, precision, coefficient, bit
and asserted value, and for every contraction scale. The machine neither receives the scale nor
constructs the full scalar representative.

The two-word entry point also accepts the protected assignment word on its separate tape, as
required by the stopping-circuit simulator. Copying that word is charged linearly; the remaining
polynomial depends only on the scalar query.
-/

public section

namespace Turing.MultiTapeATM.ScalarInput

open MultiTapeTM Cslib.GaloisRingArith
open Cslib.Circuits.Frontier.FastContraction (representative modulus)
open Cslib.Circuits.Frontier.FastContraction.ScalarInput

/-- A fixed finite native alternating machine decides claims about actual scalar input bits.
All machine data and clock constants precede every runtime input and the semantic scale. -/
theorem exists_evaluator :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (runner : MultiTapeATM (k + 2) Bool S) (c d : ℕ),
      ∀ (q : Input) (m : ℕ) (outer : List Bool),
        let clock := c * ((encInput q).length + 1) ^ d
        let cfg := (WorkTapePredicate.config outer (encInput q)).withState
          (some runner.toPTM.toNTM.q₀)
        runner.HaltsWithin clock cfg ∧
          (runner.AcceptsWithin clock cfg ↔
            ((representative m q.precision
              ((q.integer : Ring q.precision (modulus m)) * 2 ^ q.shift)).coeff
                q.coefficient).val.testBit q.bit = q.claim) := by
  obtain ⟨k, S, hS, runner, c, d, hrunner⟩ :=
    WorkTapePredicate.exists_alternating_of_polyTime computableInPolyTime_accept
  refine ⟨k, S, hS, runner, c, d, ?_⟩
  intro q m outer
  obtain ⟨ha, hh⟩ := hrunner q outer
  refine ⟨hh, ha.trans ?_⟩
  simp only [accept, decide_eq_true_eq, run_eq_representative_bit m]

/-- The same scalar decision starts from the two-word leaf layout of the stopping simulation.
The complete raw assignment is copied only a fixed number of times. All remaining work is
polynomial in the binary scalar query, with one finite machine for every scale and input. -/
theorem exists_evaluator_on_words :
    ∃ (K : ℕ) (assignment query : Fin K) (S : Type) (_ : Finite S)
      (runner : MultiTapeATM K Bool S) (C D : ℕ), assignment ≠ query ∧
      ∀ (outer raw : List Bool) (q : Input) (m : ℕ),
        let cfg := (TwoWordInput.ready assignment query outer raw (encInput q)).withState
          (some runner.toPTM.initial)
        let time := C * (raw.length + (encInput q).length ^ D + 1)
        runner.HaltsWithin time cfg ∧
          (runner.AcceptsWithin time cfg ↔
            ((representative m q.precision
              ((q.integer : Ring q.precision (modulus m)) * 2 ^ q.shift)).coeff
                q.coefficient).val.testBit q.bit = q.claim) := by
  obtain ⟨d, e, hd⟩ := computableInPolyTime_accept.exists_degree
  have hc := hd.inO.comp (ComputableInDegree.snd encBits encInput).inO_one
  obtain ⟨K, assignment, query, S, hS, runner, c, hne, hrunner⟩ :=
    TwoWordPredicate.exists_of_inO hc
  let minor (a : List Bool × Input) :=
    2 * (encInput a.2).length + ((encInput a.2).length + 1) ^ d + 3
  have hminor : PolyBounded (fun a : List Bool × Input => (encInput a.2).length) minor := by
    dsimp only [minor]
    exact (((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.self.add (.const 1)).pow d)).add (.const 3)
  obtain ⟨C, D, hbound⟩ := hminor.exists_le_linear_add_pow (fun a => a.1.length) 4
    (fun a => by simp [encInput_apply, encInputFields, encBool_apply])
  refine ⟨K, assignment, query, S, hS, runner, c * C, D, hne, ?_⟩
  intro outer raw q m cfg time
  have hs := hrunner outer raw q
  have htime : c * ((encPair encBits encInput (raw, q)).length +
      ((encPair encBits encInput (raw, q)).length + ((encInput q).length + 1) ^ d) + 1) ≤
      time := by
    calc
      _ = c * (4 * raw.length + minor (raw, q)) := by
        simp only [length_encPair, encBits_apply, minor]
        ring
      _ ≤ c * (C * (raw.length + (encInput q).length ^ D + 1)) :=
        Nat.mul_le_mul_left c (hbound (raw, q))
      _ = time := by dsimp only [time]; ring
  refine ⟨hs.1.mono htime, ?_⟩
  have ha : runner.AcceptsWithin time cfg ↔ accept q = true :=
    ⟨fun h => hs.2.mp (h.of_halted_stepCoins hs.1), fun h => (hs.2.mpr h).mono htime⟩
  exact ha.trans (by simp only [accept, decide_eq_true_eq, run_eq_representative_bit m])

end Turing.MultiTapeATM.ScalarInput
