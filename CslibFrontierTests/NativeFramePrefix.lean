/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-! # Ordinary-import clients of native framed-header extraction -/

set_option linter.privateModule false

namespace CslibFrontierTests.NativeFramePrefix
open Turing.MultiTapeTM

/-- A header and an arbitrary read-only suffix. -/
public structure Packet where
  /-- The extracted word, possibly empty. -/
  header : List Bool
  /-- The untouched remainder. -/
  suffix : List Bool

/-- Framed header then raw suffix, with no bound on either length. -/
enc_structure encPacket : Packet where header : encBits, suffix : encBits

example (p : Packet) : encPacket p = frame p.header ++ p.suffix := rfl

-- A single actual zero-workspace native machine handles every header and suffix length.
example : ComputableInTimeAndSpace Packet.header encPacket encBits
    (fun p => 2 * (encPacket p).length + 3) (fun _ => 0) :=
  .framedPrefix Packet.header encPacket encBits Packet.suffix (fun _ => rfl)

-- A compositional caller retains only the header, with no suffix-length workspace charge.
example : ComputableInSpace Packet.header encPacket encBits (fun p => p.header.length) :=
  .framedPrefix Packet.header encPacket encBits Packet.suffix (fun _ => rfl)

-- The layout premise is a checked encoding equality, including the empty header.
example (tail : List Bool) : encPacket ⟨[], tail⟩ = [false] ++ tail := rfl

end CslibFrontierTests.NativeFramePrefix
