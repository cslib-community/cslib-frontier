/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Initialize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Initializing a quantified root request stored on a work tape

The root schedule may have been guessed by preceding stages. Its work word is rewound, copied
and framed together with the computed flags. The ambient read-only input and its left-blank
position survive, so tensor continuations can read the original source input directly.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance.Initialize

open MultiTapeTM
open RootBalanceRequest (Public encPublic)

private theorem rewind_clock (c d : ℕ) : ∃ C E, ∀ p : Public,
    (encPublic p).length + c * (p.1.raw.length + shortSize p ^ d + 1) + 8 +
        (frame (encPublic p)).length ≤ C * (p.1.raw.length + shortSize p ^ E + 1) := by
  let small (p : Public) := 18 * (shortSize p + 2) + c * (shortSize p ^ d + 1) + 9
  have h : PolyBounded shortSize small := (((PolyBounded.const 18).mul
    (PolyBounded.self.add (.const 2))).add ((PolyBounded.const c).mul
      ((PolyBounded.self.pow d).add (.const 1)))).add (.const 9)
  obtain ⟨C, E, hc⟩ := h.exists_le_linear_add_pow (fun p => p.1.raw.length) (12 + c)
    (fun p => by simp [shortSize])
  refine ⟨C, E, fun p => le_trans ?_ (hc p)⟩
  have hp : (encPublic p).length ≤ 4 * p.1.raw.length + 6 * (shortSize p + 2) := by
    simp only [encPublic, length_encPair, RootPredecessorQuery.length_encInput,
      encNat_apply, Nat.size_eq_bits_len, shortSize, RootPredecessorQuery.shortSize]
    omega
  simp only [length_frame, small, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Run the flag initializer from a public word on a work tape, preserving the host input. -/
theorem exists_prepend_work {flags : Public → List Bool} {d : ℕ}
    (hd : ComputableInO (fun p : Public => (p, flags p)) encPublic RootBalanceRequest.encInput
      (fun p => p.1.raw.length + shortSize p ^ d) (fun p => p.1.raw.length + shortSize p ^ d))
    {K : ℕ} {L : Type} [Finite L] (tape : Fin K) (leaf : MultiTapeATM K Bool L) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (p : Public) (pos : ℕ), pos ≤ (encPublic p).length → ∀ (t : ℕ),
        let w := encPublic p
        let pre := frame w
        let target := WordGameLeaf.config tape (some leaf.toPTM.initial) (pre ++ flags p) pre.length
          (TwoWordLoad.blank K host)
        let start := SharedWordFork.start src atm host w pos
        leaf.HaltsWithin t target →
          let time := C * (p.1.raw.length + shortSize p ^ E + 1) + t
          atm.HaltsWithin time start ∧
            (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t target) := by
  obtain ⟨U, src, Q, hQ, atm, c, h⟩ := FramedPrefixInput.exists_prepend_work hd tape leaf
  obtain ⟨C, E, hc⟩ := rewind_clock c d
  refine ⟨U, src, Q, hQ, atm, C, E, ?_⟩
  intro host p pos hpos t
  dsimp only
  intro hh
  obtain ⟨hh', ha⟩ := h host p pos hpos t hh
  have hb : pos + c * (p.1.raw.length + shortSize p ^ d + 1) + 8 +
      ((frame (encPublic p)).length + t) ≤
      C * (p.1.raw.length + shortSize p ^ E + 1) + t := by
    have hz := hc p
    omega
  exact ⟨hh'.mono hb, ⟨fun hx => ha.mp (hx.of_halted_stepCoins hh'),
    fun hx => (ha.mpr hx).mono hb⟩⟩

end Turing.MultiTapeATM.RootPackingBalance.Initialize
