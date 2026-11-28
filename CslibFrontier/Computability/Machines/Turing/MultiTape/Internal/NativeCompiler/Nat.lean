/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Reverse
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines

/-!
# Named native binary-natural primitives

This module retains the existing streaming successor, predecessor and zero-test transducers as
`NativeCompiler`s. The wrappers name the concrete machines and their constructive state encodings;
they do not extract a witness from the existential complexity certificates.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.natSucc`: retained binary successor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natPred`: retained saturating binary predecessor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natIsZeroBool`, `.natIsZeroTest`: retained binary
  zero tests in Boolean and branch-test encodings.
* `Turing.MultiTapeTM.Internal.NativeCompiler.bitsToNat`: retained canonicalization of an
  arbitrary little-endian bit word.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Canonicalize an arbitrary little-endian bit word by reversing it, dropping its high zero
digits, and reversing it back. The retained composition computes `ofBits`, including on empty and
noncanonical input words. -/
@[expose] def bitsToNat :
    NativeCompiler ofBits encBits encNat := by
  let reverseBits : NativeCompiler List.reverse encBits encBits :=
    { tapeCount := 0
      State := Bool
      table := MultiTapeMachine.reverseInput Bool
      stateEncoding := Universal.eBit
      time := fun word => 2 * word.length + 2
      workspace := fun _ => 0
      computes := fun word => by
        simpa only [encBits_apply, reverseInput] using ReverseInput.computesTidily word }
  let dropLeadingFalses :
      NativeCompiler (fun word : List Bool => word.dropWhile (!·)) encBits encBits :=
    ofTransducer dropFalsesT Universal.eBit fun word => by
      change dropFalsesT.run false word = word.dropWhile (!·)
      exact dropFalsesT_run word
  exact (reverseBits.comp (dropLeadingFalses.comp reverseBits)).ofOutputEq fun word => by
    rw [encNat_apply, bits_ofBits]
    rfl

/-- Binary successor through the public carry transducer. -/
@[expose] def natSucc :
    NativeCompiler (fun n : ℕ => n + 1) encNat encNat :=
  ofTransducer NatSucc.succTransducer Universal.eBit fun n => by
    simpa only [encNat_apply] using NatSucc.run_succTransducer_q₀ n

/-- Saturating binary predecessor through the public borrow transducer. -/
@[expose] def natPred :
    NativeCompiler (fun n : ℕ => n - 1) encNat encNat :=
  ofTransducer NatPred.predTransducer (optionStateEncoding Universal.eBit) fun n => by
    simpa only [encNat_apply] using NatPred.run_predTransducer_q₀ n

/-- Binary zero test with one-bit Boolean output. -/
@[expose] def natIsZeroBool :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encBool :=
  ofTransducer NatPred.isZeroTransducer Universal.eBit fun n => by
    simpa only [encNat_apply, encBool_apply] using NatPred.run_isZeroTransducer_q₀ n

/-- Binary zero test in the empty/nonempty branch encoding, including the retained conversion. -/
@[expose] def natIsZeroTest :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encTest :=
  boolToTest.comp natIsZeroBool

end Turing.MultiTapeTM.Internal.NativeCompiler
