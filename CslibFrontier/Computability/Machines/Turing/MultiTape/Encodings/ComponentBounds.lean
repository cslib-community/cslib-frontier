/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.ComponentBounds.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi

/-!
# Component bounds without unfolding encodings

Use `simp only [enc_component]` for pair projections, finite-table entries, list lengths
and encoded suffixes.
For a list element supply its membership proof, as in `simp only [enc_component, hm]`.
The list rules use `SizedListEncoding`, so they also apply to readable encodings other than
`encList`. The set is opt-in and does not expand words or replace nonlinear arithmetic.

The sparse CNF compiler uses these rules to obtain element bounds before transporting them
through its enclosing pair and polynomial growth estimates.
-/

attribute [enc_component] Turing.MultiTapeTM.length_le_encPair_left
  Turing.MultiTapeTM.length_le_encPair_right
  Turing.MultiTapeTM.SizedListEncoding.length_le
  Turing.MultiTapeTM.SizedListEncoding.length_elem_le
  Turing.MultiTapeTM.SizedListEncoding.length_drop_le

attribute [enc_component] Turing.MultiTapeTM.length_le_encPi
