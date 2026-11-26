/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Unsigned Little-Endian Binary Symbol Codec for `ZMod p`

Defines the computable unsigned little-endian binary symbol encoding `encZMod` and decoding
`decZMod` on `ZMod p` together with `leftInverse_decZMod_encZMod` for instantiating BCS
random-oracle soundness bounds over prime fields.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

section SymbolEncoding

/-- Computable unsigned little-endian binary symbol encoding for `ZMod p` via `Nat.bits`,
preserving the minimal bit-list word layout `Nat.bits x.val` (distinct from the sign-magnitude
`ZMod` encoding in `Turing.MultiTapeTM.encZMod`). -/
@[expose] def encZMod {p : ℕ} (x : ZMod p) : List Bool :=
  Nat.bits x.val

/-- Computable unsigned little-endian binary symbol decoding for `ZMod p` via
`Turing.MultiTapeTM.ofBits`. -/
@[expose] def decZMod (p : ℕ) (bs : List Bool) : ZMod p :=
  (Turing.MultiTapeTM.ofBits bs : ZMod p)

/-- Round-trip inversion: `decZMod p` is a left inverse to `encZMod`. -/
theorem leftInverse_decZMod_encZMod (p : ℕ) [NeZero p] :
    Function.LeftInverse (decZMod p) (encZMod (p := p)) := by
  intro x
  simp only [decZMod, encZMod, Turing.MultiTapeTM.ofBits_bits, ZMod.natCast_zmod_val]

end SymbolEncoding

end Cslib.Crypto.Protocols.FRI
