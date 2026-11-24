/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.Hybrid

/-!
# Cascade evaluation and prefix hybrid tests

Use one-bit message blocks and a two-bit key to exercise the separate widths and the extension
identity. The hybrid examples exercise mixed-length queries and prefix reuse.
-/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

private def toggle (key block : List Bool) : List Bool :=
  if block.headD false then key.map (!·) else key

example : cascadeFamily (fun _ => 1) toggle [true, false] [] = [true, false] :=
  cascadeFamily_nil _ _ _

example : cascadeFamily (fun _ => 1) toggle [true, false] [true, false] = [false, true] := by
  decide

example : cascadeFamily (fun _ => 1) toggle [true, false] ([true] ++ [true, false]) =
    cascadeFamily (fun _ => 1) toggle (cascadeFamily (fun _ => 1) toggle [true, false] [true])
      [true, false] :=
  cascadeFamily_append (fun key block _ => by
    unfold toggle
    split <;> simp) _ (by decide) (by decide) (by decide)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool => cascadeFamily (fun _ => 1) (fun key _ => key) p.1 p.2)
    (encPair encBits encBits) encBits :=
  computableInPolyTime_cascadeFamily (ComputableInPolyTime.const 1) (fun _ _ _ => rfl)
    (ComputableInPolyTime.fst encBits encBits)

private def boundedWords (_ : ℕ) (word : List Bool) : Bool := decide (word.length ≤ 2)

private def compareReplies : OracleDistinguisher := fun _ _ => do
  let empty ← ProbOracleComp.query ((), [])
  let twoBits ← ProbOracleComp.query ((), [true, false])
  let repeated ← ProbOracleComp.query ((), [true, false])
  let malformed ← ProbOracleComp.query ((), [true, false, true])
  return empty != twoBits && twoBits == repeated && malformed.isEmpty

-- The final hybrid handles different valid lengths, a repeat, and an invalid word.
example :
    ProbComp.eval (cascadePrefixHybridGame boundedWords (fun _ => 1) toggle compareReplies 2 2) =
      ProbComp.eval (prfIdealGameOn boundedWords id compareReplies 2) :=
  eval_cascadePrefixHybridGame_eq_ideal _ _ fun query hquery => by
    simpa [boundedWords] using hquery

-- At one block of depth, distinct queries sharing a first block reuse its sampled label.
example :
    ProbComp.eval (prefixHybridOracle (boundedWords 2) (cascadeFamily (fun _ => 1) toggle)
        2 1 [true, true] [([true], [true, false])]) =
      PMF.pure ([false, true], [([true], [true, false])]) := by
  simp [prefixHybridOracle, boundedWords, ProbComp.eval_pure, memoize, cascadeFamily,
    BitString.listRows, BitString.listRow, toggle]
