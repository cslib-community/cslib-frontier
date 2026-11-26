/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterProgram
public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Encoding

/-!
# Encodings of guarded register programs

Control labels and register addresses use binary naturals. The initial register contents are
stored explicitly as a raw bit list. The two finite edge lists retain their original order.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

open _root_.Turing.MultiTapeTM

/-- Framed binary source, target and register, followed by the framed guard and written bit. -/
enc_structure encInstruction : Instruction where
  source : encNat, target : encNat, register : encNat, guard : encBool, write : encBool

/-- Framed instruction list, jumps, raw initial bits and binary start, then binary target. -/
enc_structure encProgram : Program where
  instructions : (encList encInstruction), jumps : (encList encTunnel), initial : encBits,
    start : encNat, target : encNat

end Cslib.Complexity.SelfClosingDoor.RegisterProgram
