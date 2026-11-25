/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Computability.Circuit.Boolean.CycleMinorLowerBound
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-! Concrete `module` clients for the transfer theorems of the cycle-and-minor function at `d = 6`,
with cuts of between `2` and `4` of the `6` coordinates (`⌈d / 3⌉` and `⌊2 d / 3⌋`) over `F₂`. -/

public section

namespace CslibFrontierTests.CycleMinorLowerBound

open Cslib.Circuits Cslib.BranchingPrograms

/-- The main theorem: a syntactically multilinear circuit with `s` gates computing the multilinear
representative of the function bounds the cut cover number by `2 s + 1` and the component size of
`HC_6` by `s + 1`. -/
example (A : Circuit (arithSignature (ZMod 2)) (cmInputs 6) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn 6)) :
    cutCover (ZMod 2) 6 2 4 ≤ 2 * A.size + 1 ∧ hcComponentSize (ZMod 2) 6 ≤ A.size + 1 :=
  measures_le_of_syntacticallyMultilinear A hA hf (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- A d-D with `s` gates computing the function bounds the cut cover number by `8 s + 1` and the
component size of `HC_6` by `4 s + 1`. -/
example (c : Circuit Boolean.signature (cmInputs 6) 1) (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn 6))) :
    cutCover (ZMod 2) 6 2 4 ≤ 8 * c.size + 1 ∧ hcComponentSize (ZMod 2) 6 ≤ 4 * c.size + 1 :=
  ⟨hc.cutCover_le hf (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc.hcComponentSize_le hf⟩

/-- A read-once parity program with `w` wires computing the function bounds the cut cover number
by `2 (2 + 5 w) + 1` and the component size of `HC_6` by `2 + 5 w + 1`. -/
example {n : ℕ} (P : NBP (Fin (cmInputs 6)) Bool n) (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn 6 z = true) :
    cutCover (ZMod 2) 6 2 4 ≤ 2 * (2 + 5 * P.wireCount) + 1 ∧
      hcComponentSize (ZMod 2) 6 ≤ 2 + 5 * P.wireCount + 1 :=
  ⟨NBP.cutCover_le hP hf (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    NBP.hcComponentSize_le hP hf⟩

end CslibFrontierTests.CycleMinorLowerBound
