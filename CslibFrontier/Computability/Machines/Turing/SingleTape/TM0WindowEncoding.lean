/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.TM0Window
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-!
# Structural encoding of finite tape windows

A configuration encodes its finite control, scanned cell and nearest-first tape lists.

## Main definitions

* `Turing.TM0Window.encCfg`: the structural encoding of a window configuration.
-/

public section

noncomputable section

namespace Turing.TM0Window
open Turing.MultiTapeTM
variable {Γ Q : Type} [Finite Γ] [Finite Q]

/-- Structural encoding of finite control, scanned cell, and the nearest-first tape lists. -/
enc_structure encCfg : Cfg Γ Q where
  state : (encFinite Q), scanned : (encFinite Γ),
  left : (encList (encFinite Γ)), right : (encList (encFinite Γ))

end Turing.TM0Window

end
