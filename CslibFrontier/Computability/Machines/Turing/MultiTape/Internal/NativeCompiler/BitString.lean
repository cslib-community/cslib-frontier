/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BitListCodec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-!
# Named native raw-bit lookup

This definitions-only module retains binary-indexed access to a raw bit word. The concrete
compiler first inserts the standard Boolean-list framing with the shared finite-state codec, then
reuses the retained single-pass binary list lookup. Out-of-range indices return the caller-supplied
fallback.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.bitsGetDNatCompiler`: total binary-indexed lookup in
  a raw bit word.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Internal

/-- Binary-indexed access to a raw bit word, with an explicit out-of-range fallback. The compiler
retains the framing conversion and the complete framed-list scan. -/
@[expose] noncomputable def bitsGetDNatCompiler (fallback : Bool) :
    NativeCompiler (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encNat) encBool := by
  let encInput := encPair encBits encNat
  let bits := first encBits encNat
  let index := second encBits encNat
  let convert : NativeCompiler (fun word : List Bool =>
      bitsToBoolListT.run bitsToBoolListT.q₀ word)
      encBits encBits :=
    ofTransducer bitsToBoolListT Universal.eBit fun _ => rfl
  let listed : NativeCompiler (id : List Bool → List Bool) encBits (encList encBool) :=
    ((convert.comp (encodeFrame encBits)).ofOutputEq fun word => by
      simpa only [id_eq, encBits_apply] using (bitsToBoolListT_run word).symm)
  let listedInput := listed.comp bits
  exact (listGetDNatCompiler fallback encBool).comp (listedInput.pair index)

end Turing.MultiTapeTM.Internal.NativeCompiler
