/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP
public import CslibFrontier.Foundations.Data.MvPolynomial.SplitRank

/-!
# Split rank of any-order read-once oblivious algebraic branching programs

Given a split of the variables, read all variables on the first side before all variables on
the other side. The matrix product factors at the cut, expressing each entry as a sum of as
many separated products as the width of the program.
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {F : Type*} [Field F] {n w : ℕ}

/-- Nisan's observation: a polynomial computed by width-`w` read-once oblivious branching
programs in every order has split rank at most `w` across every split of the variables. -/
theorem IsAnyOrderROABP.splitRankLE {f : MvPolynomial (Fin n) F} (hf : IsAnyOrderROABP w f)
    (U : Finset (Fin n)) : SplitRankLE (U : Set (Fin n)) w f := by
  classical
  obtain ⟨M, s, t, rfl⟩ := hf (U.toList ++ Uᶜ.toList)
    (List.Nodup.append U.nodup_toList Uᶜ.nodup_toList fun i hi hi' =>
      (mem_compl.1 (mem_toList.1 hi')) (mem_toList.1 hi))
    (fun i => List.mem_append.2 ((em (i ∈ U)).imp mem_toList.2 fun h =>
      mem_toList.2 (mem_compl.2 h)))
  refine ⟨fun k => roabpProd M U.toList s k, fun k => roabpProd M Uᶜ.toList k t,
    fun k => roabpProd_mem_supported M _ (fun i hi => mem_coe.2 (mem_toList.1 hi)) _ _,
    fun k => roabpProd_mem_supported M _
      (fun i hi => fun h => mem_compl.1 (mem_toList.1 hi) (mem_coe.1 h)) _ _, ?_⟩
  rw [roabpProd, List.map_append, List.prod_append, Matrix.mul_apply]
  rfl

end Cslib.Circuits.Arithmetic
