/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.IntBinary

/-! Checked generic clients for retained signed-binary arithmetic. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerIntBinary

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- The composed client retains the actual machine and its exact time and workspace maps. -/
example :
    let compiler :
        NativeCompiler (fun input : ℤ × ℤ => decide (0 < input.1 - input.2))
          (encPair encIntBin encIntBin) encBool :=
      intBinIsPosBool.comp intBinSub
    compiler.table.toTM.ComputesFunInTimeAndSpace
      (encPair encIntBin encIntBin) encBool
      (fun input : ℤ × ℤ => decide (0 < input.1 - input.2))
      compiler.time compiler.workspace := by
  exact (intBinIsPosBool.comp intBinSub).computesInTimeAndSpace

/-- The same composed client retains a first-order description of its actual transition table. -/
example :
    let compiler :
        NativeCompiler (fun input : ℤ × ℤ => decide (0 < input.1 - input.2))
          (encPair encIntBin encIntBin) encBool :=
      intBinIsPosBool.comp intBinSub
    ∀ (state : compiler.State) (input : Option Bool)
        (work : Fin compiler.tapeCount → Option Bool),
      compiler.description.Holds (compiler.table.toTM.map compiler.stateEncoding Universal.eBit)
        (compiler.stateEncoding state) (input.map Universal.eBit)
        (Option.map Universal.eBit ∘ work) := by
  exact fun state input work =>
    (intBinIsPosBool.comp intBinSub).description_holds state input work

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerIntBinary
