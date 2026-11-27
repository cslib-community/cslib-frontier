/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.Packed.RawControllerNative
public import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Exact register points requested by the raw controller

Dropping the target register and concatenating the remaining bank in cyclic order gives the
existing typed child-register point, with the original modulus padding on every cell.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

/-- The physical request point contains exactly the cyclic typed registers, still padded. -/
theorem point_ofRegs {p d r : ℕ} (S : Ary.State (ZMod p) d r) (t : Fin (d + 1)) :
    point d r t.val (ofRegs S) = List.ofFn
      (fun a : Fin (d * r) => p +
        (Cslib.BitString.blocksEquiv.symm (fun j => S (Ary.reg t j)) a).val) := by
  have hlength := length_point (ofRegs S) (length_ofRegs S) t
  refine List.ext_getElem (hlength.trans List.length_ofFn.symm) fun a ha hb => ?_
  simp only [List.getElem_ofFn, Cslib.BitString.blocksEquiv_symm_apply]
  obtain ⟨⟨j, i⟩, hpair⟩ := finProdFinEquiv.surjective ⟨a, List.length_ofFn ▸ hb⟩
  have ha_eq : a = index r j i := (congrArg Fin.val hpair).symm
  rw [← hpair, Equiv.symm_apply_apply, ← List.getD_eq_getElem _ 0 ha, ha_eq,
    point_getD (ofRegs S) (length_ofRegs S) t j i, reg_eq]
  erw [ofRegs, List.getD_ofFn_of_lt _ (finProdFinEquiv (Ary.reg t j, i)).isLt 0]
  simp only [Fin.eta, Equiv.symm_apply_apply]

end Cslib.TreeEval.Ary.Packed.RawController
