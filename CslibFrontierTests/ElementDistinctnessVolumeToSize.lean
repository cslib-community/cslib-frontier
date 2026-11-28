/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.VolumeToSize
import CslibFrontier.Computability.Circuit.Frontier.Compiler.OpenBitNetwork
import CslibFrontier.Computability.Circuit.InnerSize
import Mathlib.Data.ZMod.Basic

/-! Pin four three-bit records down to two one-bit records. This uses all two available fixed
names, both Boolean answers, and coefficients in characteristic two. -/

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ElementDistinctness
  Cslib.Circuits.Frontier

example :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork (ZMod 2) (Fin 2) V E), M.Trivalent ∧
        M.contraction ![false, true] = 1 ∧ M.contraction ![true, true] = 0 := by
  obtain ⟨C, hc, _⟩ := exists_computes_size_eq_complexity (I := fullInterpretation (k := 2))
    (f := single (elementDistinctness 4 3))
  obtain ⟨V, E, iV, iE, dE, N, ht, _, heval⟩ :=
    Compiler.exists_trivalent_openBitNetwork C fullInterpretation (ZMod 2)
      C.fanInAtMost_fullSignature
  obtain ⟨M, _, hM, _, h⟩ := exists_pin_distinctness (m := 2) (k := 1)
    (by decide) (by decide) (by decide) N ht fun x => by
      simpa only [hc x, single] using heval x
  refine ⟨V, E, iV, iE, dE, M, hM, ?_, ?_⟩
  · rw [h, show elementDistinctness 2 1 ![false, true] = true by decide]
    rfl
  · rw [h, show elementDistinctness 2 1 ![true, true] = false by decide]
    rfl
