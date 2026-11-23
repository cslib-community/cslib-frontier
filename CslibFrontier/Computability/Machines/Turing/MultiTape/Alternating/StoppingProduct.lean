/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ProtectedWordGame
public import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteBounds
import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteTime

/-!
# Native navigation through a stopping product

The short Boolean position is updated by native routing rounds on a separate tape block. The
assignment is retained on a protected terminal tape and is never copied by a routing round.
-/

public section

namespace Turing.MultiTapeATM.StoppingProduct

open MultiTapeTM Cslib GaloisRingArith Cslib.Circuits.Frontier.FastContraction
open StoppingQuery.ProductRouting

/-- All native routing rounds and the initial header computation, plus one terminal evaluation.
The polynomial is applied only to short metadata; the retained assignment is not in this clock. -/
@[expose] noncomputable def clock (C D : ℕ) (parameters : StoppingQuery.Product.Parameters)
    (terminalTime : ℕ) : ℕ :=
  let levels := Nat.clog 2 parameters.vertices
  let moves := 13 * (levels *
    (SignedValueGame.height (3 ^ modulusExp parameters.scale) parameters.precision +
      2 * SignedValueGame.rounds parameters.precision + 11) + 1) + 12
  (moves + 1) * (C * (metadataBound parameters (2 ^ levels) levels + 1) ^ D + 2) +
    terminalTime + 1

/-- Compile the balanced stopping product into one fixed finite alternating machine. The raw
entry consists of an opaque assignment word and the short encoded root position on two distinct
work tapes. Native header preparation and every Boolean routing round are included in the clock.

The supplied terminal is invoked only on a terminal gate and receives the retained assignment
and the terminal position. Its time is added once per branch. Arithmetic routing is constructed
from the concrete product compiler and requires no caller-supplied decoder or update certificate. -/
theorem exists_evaluator {N : ℕ} {S : Type} [Finite S]
    (assignment query : Fin N) (hne : assignment ≠ query) (terminal : MultiTapeATM N Bool S) :
    ∃ (U : ℕ) (assignmentSource querySource : Fin U) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM U Bool Q) (C D : ℕ), assignmentSource ≠ querySource ∧
      ∀ (input word : List Bool) (parameters : StoppingQuery.Product.Parameters)
        (entry : ℕ → ℕ → GaloisRingArith.Ring parameters.precision (modulus parameters.scale))
        (terminalTime : ℕ),
        (∀ p, Valid parameters (2 ^ Nat.clog 2 parameters.vertices)
            (Nat.clog 2 parameters.vertices) p → player p = none →
          let start := (TwoWordInput.ready assignment query input word (encPosition p)).withState
            (some terminal.toPTM.initial)
          terminal.HaltsWithin terminalTime start ∧
            (terminal.AcceptsWithin terminalTime start ↔
              StoppingQuery.value parameters.scale parameters.precision 0 parameters.vertices
                entry (address p) = p.claim)) →
        ∀ (coefficient : Fin (modulus parameters.scale).length)
          (bit : Fin parameters.precision) (claim : Bool),
          let position := root parameters coefficient.val bit.val claim
          let start := (TwoWordInput.ready assignmentSource querySource input word
            (encPosition position)).withState (some atm.toPTM.initial)
          atm.HaltsWithin (clock C D parameters terminalTime) start ∧
            (atm.AcceptsWithin (clock C D parameters terminalTime) start ↔
              ((representative parameters.scale parameters.precision
                (∏ vertex ∈ Finset.range parameters.vertices, entry 0 vertex)).coeff
                  coefficient.val).val.testBit bit.val = claim) := by
  obtain ⟨U, ass, src, Q, hQ, atm, C, D, hne', he⟩ :=
    ProtectedWordGame.exists_evaluator encPosition player StoppingQuery.ProductRouting.next
      player_polyTime step_polyTime assignment query hne terminal
  refine ⟨U, ass, src, Q, hQ, atm, C, D, hne', ?_⟩
  intro input word parameters entry terminalTime hterminal coefficient bit claim position start
  let levels := Nat.clog 2 parameters.vertices
  let bound := metadataBound parameters (2 ^ levels) levels
  let valid := Valid parameters (2 ^ levels) levels
  let value := fun p : Position => StoppingQuery.value parameters.scale parameters.precision 0
    parameters.vertices entry (address p) = p.claim
  let rank := fun p : Position => StoppingQuery.rank parameters.scale parameters.precision 0
    parameters.vertices (address p)
  have hvalid : valid position := valid_root parameters coefficient.isLt bit.isLt claim
  have hs := he input word valid value rank bound terminalTime
    (fun _ h => h.length_encPosition_le) (fun _ h _ _ move => h.next move)
    (fun p hp owner hplayer move => by
      have h := rank_next_lt p hplayer move
      rw [hp.parameters] at h
      exact h)
    (fun p hp owner hplayer => by
      have h := @value_iff_next p
      rw [hp.parameters] at h
      exact h entry hplayer)
    hterminal position hvalid
  have hrootRank := StoppingQuery.rank_block_root_le parameters.scale parameters.precision 0
    parameters.vertices 0 0 levels coefficient.val bit.val
  rw [← root_address parameters coefficient.val bit.val claim] at hrootRank
  have htime : (rank position + 1) * (C * (bound + 1) ^ D + 2) + terminalTime + 1 ≤
      clock C D parameters terminalTime := by
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.succ_le_succ hrootRank)) _) _
  have hvalue : value position ↔
      ((representative parameters.scale parameters.precision
        (∏ vertex ∈ Finset.range parameters.vertices, entry 0 vertex)).coeff
          coefficient.val).val.testBit bit.val = claim := by
    dsimp only [value, position]
    rw [root_address, StoppingQuery.value_product_root]
    rfl
  exact ⟨hs.1.mono htime, ⟨fun h => hvalue.mp (hs.2.mp (h.of_halted_stepCoins hs.1)),
    fun h => (hs.2.mpr (hvalue.mpr h)).mono htime⟩⟩

end Turing.MultiTapeATM.StoppingProduct
