/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

import CslibFrontier.Computability.Circuit.DepthReduction
import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Tests for Valiant depth reduction

Exercises `Program.valiantDepthReduction` and `Program.valiant_halving_cut` on an empty program,
a multi-layer Boolean program, and the `t = k` boundary case.
-/

namespace Cslib.Circuits.Tests.DepthReduction

open Cslib.Circuits.Boolean

example :
    ∃ cut : Finset (Fin 0),
      cut.card ≤ 2 * 1 * 0 / 1 ∧
      ∀ w : Wire 2 0, (Program.empty : Program signature 2 0).residualWireDepths cut w < 2 ^ 0 :=
  (Program.empty : Program signature 2 0).valiantDepthReduction trivial (by decide) (by decide)
    (fun w => by
      cases w with
      | input _ => simp [Program.wireDepths]
      | gate j => exact Fin.elim0 j)

private def twoLayerProg : Program signature 2 2 :=
  ((Program.empty : Program signature 2 0).gate
      ⟨Boolean.Op.and, fun i => if i = 0 then Wire.input 0 else Wire.input 1⟩).gate
    ⟨Boolean.Op.or, fun i => if i = 0 then Wire.gate ⟨0, by decide⟩ else Wire.input 0⟩

private theorem twoLayerProg_depth (w : Wire 2 2) : twoLayerProg.wireDepths w < 2 ^ 2 := by
  cases w with
  | input _ => simp [Program.wireDepths]
  | gate j =>
    cases j using Fin.cases with
    | zero => simp only [Fin.isValue, Nat.reducePow]; decide
    | succ j' =>
      cases j' using Fin.cases with
      | zero => simp only [Fin.isValue, Fin.succ_zero_eq_one, Nat.reducePow]; decide
      | succ j'' => exact Fin.elim0 j''

example :
    ∃ cut : Finset (Fin 2),
      cut.card ≤ 2 * 2 / 2 ∧
      ∀ w : Wire 2 2, twoLayerProg.residualWireDepths cut w < 2 ^ (2 - 1) :=
  twoLayerProg.valiant_halving_cut (by simp [twoLayerProg, Program.FanInAtMost]) (by decide)
    twoLayerProg_depth

example :
    ∃ cut : Finset (Fin 2),
      cut.card ≤ 2 * 2 * 2 / 2 ∧
      ∀ w : Wire 2 2, twoLayerProg.residualWireDepths cut w < 2 ^ (2 - 2) :=
  twoLayerProg.valiantDepthReduction (by simp [twoLayerProg, Program.FanInAtMost])
    (by decide) (by decide) twoLayerProg_depth

end Cslib.Circuits.Tests.DepthReduction
