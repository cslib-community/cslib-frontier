/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.Data.Polynomial.CoeffList.DivMod
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
public import CslibFrontier.Foundations.Data.Matrix.RowTable
public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
public meta import CslibFrontier.Foundations.Data.Polynomial.CoeffList.Arith
public meta import CslibFrontier.Foundations.Data.Polynomial.CoeffList.DivMod
public meta import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
public meta import CslibFrontier.Foundations.Data.Matrix.RowTable
public meta import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for `Polynomial.CoeffList.{Arith,DivMod}` and `Cslib.RowTable`

Computable `#guard` and kernel-checked theorem tests over `ℚ`, `ZMod 2`, and `ZMod 5` exercising:
1. `Polynomial.CoeffList` trimming, semiring/ring operations, formal derivative, Euclidean
   `divMod`/`div`/`mod`/`negMod`, divisibility characterization, and `gcd` over `ℚ`, `ZMod 2`, and
   `ZMod 5`, together with `Cslib.RealRoot.sturmSeqList` and `Cslib.RealRoot.sturmVariationsList`.
2. `Cslib.RowTable` shape invariants, `entry`, `tabulate`, `map`, `toMatrix`, `ofMatrix` round-trip
   identities, and `IntTable`/`RatTable` encoding layout preservation.
-/

namespace CslibFrontierTests.CoeffListRowTable

set_option linter.hashCommand false

open Cslib Cslib.LinearAlgebra Polynomial Turing.MultiTapeTM

/-! ### 1. `Polynomial.CoeffList` over `ℚ` -/

#guard CoeffList.trim [(1 : ℚ), 0, -2, 0, 0] == [1, 0, -2]
#guard CoeffList.trim [(0 : ℚ), 0, 0] == []
#guard CoeffList.add [(1 : ℚ), 2, 3] [0, -2, -3] == [1]
#guard CoeffList.sub [(1 : ℚ), 2, 3] [1, 0, 3] == [0, 2]
#guard CoeffList.smul (mkRat 1 2) [(2 : ℚ), -4, 0] == [1, -2]
#guard CoeffList.shift 2 [(0 : ℚ), 0] == []
#guard CoeffList.shift 2 [(3 : ℚ), -1] == [0, 0, 3, -1]
#guard CoeffList.mul [(1 : ℚ), 1] [-1, 1] == [-1, 0, 1]
#guard CoeffList.deriv [(5 : ℚ), -3, 2, mkRat 1 3] == [-3, 4, 1]

/-- Non-monic rational Euclidean division:
`((1 + 2 X + 3 X^2) * (2 - X) + 3/4)` divided by `2 - X` has quotient `1 + 2 X + 3 X^2` and
remainder `3/4`. -/
private def dividendQ : List ℚ :=
  CoeffList.add (CoeffList.mul [1, 2, 3] [2, -1]) [mkRat 3 4]

#guard CoeffList.divMod dividendQ [2, -1] == ([1, 2, 3], [mkRat 3 4])
#guard CoeffList.divMod dividendQ [0, 0] == ([], dividendQ)

/-- Non-monic rational GCD:
`1/2 - X + (1/2) X^2 = (1/2)(X - 1)^2` and `-2 + 2 X^2 = 2(X - 1)(X + 1)` have Euclidean GCD
`1 - X` (`[1, -1]`). -/
private def polyQ1 : List ℚ := [mkRat 1 2, -1, mkRat 1 2]
private def polyQ2 : List ℚ := [-2, 0, 2]

#guard CoeffList.gcd polyQ1 polyQ2 == [1, -1]
#guard CoeffList.mod polyQ1 [1, -1] == []
#guard CoeffList.mod polyQ2 [1, -1] == []

example :
    ofCoeffList (CoeffList.div dividendQ [2, -1]) =
      ofCoeffList dividendQ / ofCoeffList [(2 : ℚ), -1] ∧
    ofCoeffList (CoeffList.mod dividendQ [2, -1]) =
      ofCoeffList dividendQ % ofCoeffList [(2 : ℚ), -1] ∧
    ofCoeffList (CoeffList.gcd polyQ1 polyQ2) ∣ ofCoeffList polyQ1 ∧
    ofCoeffList (CoeffList.gcd polyQ1 polyQ2) ∣ ofCoeffList polyQ2 ∧
    CoeffList.mod polyQ1 [1, -1] = [] :=
  ⟨CoeffList.ofCoeffList_div _ _,
    CoeffList.ofCoeffList_mod _ _,
    CoeffList.ofCoeffList_gcd_dvd_left _ _,
    CoeffList.ofCoeffList_gcd_dvd_right _ _,
    (CoeffList.mod_eq_nil_iff_dvd polyQ1 [(1 : ℚ), -1]).mpr
      ⟨ofCoeffList [(1 / 2 : ℚ), -(1 / 2)], by
        have hhalf : C (1 / 2 : ℚ) + C (1 / 2) = 1 := by rw [← map_add]; norm_num
        have hm : mkRat 1 2 = (1 / 2 : ℚ) := by norm_num
        simp only [polyQ1, hm, ofCoeffList_cons, ofCoeffList_nil, map_neg, map_one]
        linear_combination X * hhalf⟩⟩

/-! ### 2. `Polynomial.CoeffList` over `ZMod 2` and `ZMod 5` -/

#guard CoeffList.divMod ([(1 : ZMod 2), 0, 0, 1]) [1, 1, 1] == ([1, 1], [])
#guard CoeffList.gcd ([(1 : ZMod 2), 0, 0, 1]) [1, 1, 1] == [1, 1, 1]
#guard CoeffList.deriv ([(1 : ZMod 2), 1, 1, 1]) == [1, 0, 1]

private local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

#guard CoeffList.gcd ([(4 : ZMod 5), 0, 1]) [3, 1, 1] == [1, 4]
#guard CoeffList.divMod ([(4 : ZMod 5), 0, 1]) [1, 4] == ([4, 4], [])
#guard CoeffList.mod ([(3 : ZMod 5), 1, 1]) [1, 4] == []

example :
    ofCoeffList (CoeffList.gcd [(4 : ZMod 5), 0, 1] [3, 1, 1]) ∣
      ofCoeffList [(4 : ZMod 5), 0, 1] ∧
    ofCoeffList (CoeffList.gcd [(4 : ZMod 5), 0, 1] [3, 1, 1]) ∣
      ofCoeffList [(3 : ZMod 5), 1, 1] ∧
    ∀ u : (ZMod 5)[X],
      u ∣ ofCoeffList [(4 : ZMod 5), 0, 1] →
      u ∣ ofCoeffList [(3 : ZMod 5), 1, 1] →
      u ∣ ofCoeffList (CoeffList.gcd [(4 : ZMod 5), 0, 1] [3, 1, 1]) :=
  ⟨CoeffList.ofCoeffList_gcd_dvd_left _ _,
    CoeffList.ofCoeffList_gcd_dvd_right _ _,
    fun _ ha hb => CoeffList.dvd_ofCoeffList_gcd ha hb⟩

/-! ### 3. `Cslib.RowTable` functoriality, `Matrix` bridges, and encoding layout -/

private def sampleIntTable : IntTable :=
  ⟨2, 3, [[1, -2, 3], [4, 0, -6]]⟩

#guard (sampleIntTable.map (fun z : ℤ => mkRat z 2)).rows ==
  [[mkRat 1 2, -1, mkRat 3 2], [2, 0, -3]]
#guard RowTable.tabulate 2 3 sampleIntTable.entry == sampleIntTable
#guard sampleIntTable.entry 5 1 == 0
#guard sampleIntTable.entry 1 5 == 0

example :
    sampleIntTable.WellFormed ∧
      (sampleIntTable.map (Int.castRingHom ℚ)).WellFormed ∧
      (sampleIntTable.map (Int.castRingHom ℚ)).toMatrix =
        sampleIntTable.toMatrix.map (Int.castRingHom ℚ) ∧
      RowTable.ofMatrix sampleIntTable.toMatrix = sampleIntTable := by
  have hwf : sampleIntTable.WellFormed := by decide
  exact ⟨hwf, hwf.map _, RowTable.toMatrix_map _ (map_zero _) sampleIntTable,
    RowTable.ofMatrix_toMatrix hwf⟩

example (A : Matrix (Fin 2) (Fin 3) ℚ) :
    (RowTable.ofMatrix A).toMatrix = A ∧
      ((RowTable.ofMatrix A).map (2 * ·)).toMatrix = A.map (2 * ·) :=
  ⟨RowTable.toMatrix_ofMatrix A, by simp [RowTable.toMatrix_map]⟩

/-- Encoded words of `IntTable.enc` and `RatTable.enc` are unchanged under the `RowTable`
abbreviations (`rfl`). -/
example (T : IntTable) (M : RatTable) :
    IntTable.enc T =
      encPair encUnary (encPair encUnary (encList (encList encIntBin)))
        (T.numRows, T.numCols, T.rows) ∧
    RatTable.enc M =
      encPair encUnary (encPair encUnary (encList (encList encRat)))
        (M.numRows, M.numCols, M.rows) :=
  ⟨rfl, rfl⟩

/-! ### 4. `CoeffList.negMod` and `RealRoot.sturmSeqList` / `sturmVariationsList` -/

#guard CoeffList.negMod dividendQ [2, -1] == [-mkRat 3 4]
#guard CoeffList.negMod [(-2 : ℚ), 0, 1] [0, 2] == [2]
#guard CoeffList.negMod ([(2 : ZMod 5), 0, 1]) [1, 1] == [2]
#guard RealRoot.sturmSeqList [(-2 : ℚ), 0, 1, 0, 0] == [[-2, 0, 1], [0, 2], [2]]
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-2 : ℚ), 0, 1, 0, 0]) (-2) == 2
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-2 : ℚ), 0, 1, 0, 0]) 0 == 1
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-2 : ℚ), 0, 1, 0, 0]) 2 == 0
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-6 : ℚ), 11, -6, 1]) 0 == 3
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-6 : ℚ), 11, -6, 1]) (mkRat 3 2) == 2
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-6 : ℚ), 11, -6, 1]) (mkRat 5 2) == 1
#guard RealRoot.sturmVariationsList (RealRoot.sturmSeqList [(-6 : ℚ), 11, -6, 1]) 4 == 0

example (cs : List ℚ) (x : ℚ) :
    (CoeffList.trim cs).Sublist cs ∧
      ofCoeffList (CoeffList.negMod cs [1, 1]) = -ofCoeffList cs % ofCoeffList [(1 : ℚ), 1] ∧
      (RealRoot.sturmSeqList cs).map ofCoeffList =
        Polynomial.sturmSeq (ofCoeffList cs) (derivative (ofCoeffList cs)) ∧
      RealRoot.sturmVariationsList (RealRoot.sturmSeqList cs) x =
        Polynomial.sturmVariations ((ofCoeffList cs).map (algebraMap ℚ ℝ)) (x : ℝ) :=
  ⟨CoeffList.trim_sublist cs,
    CoeffList.ofCoeffList_negMod cs [1, 1],
    RealRoot.sturmSeqList_map_ofCoeffList cs,
    RealRoot.sturmVariationsList_eq_sturmVariations cs x⟩

public section

/-- Exported check that `CoeffList.mod_eq_nil_iff_dvd` over `ℚ` and `RowTable.ofMatrix_toMatrix`
compose cleanly. -/
theorem smoke_coeffList_and_rowTable :
    CoeffList.mod [(mkRat 1 2), -1, mkRat 1 2] [1, -1] = [] ∧
      RowTable.ofMatrix (RowTable.mk 2 2 [[(1 : ℤ), 2], [3, 4]]).toMatrix =
        RowTable.mk 2 2 [[(1 : ℤ), 2], [3, 4]] :=
  ⟨(CoeffList.mod_eq_nil_iff_dvd _ _).mpr
      ⟨ofCoeffList [(1 / 2 : ℚ), -(1 / 2)], by
        have hhalf : C (1 / 2 : ℚ) + C (1 / 2) = 1 := by rw [← map_add]; norm_num
        have hm : mkRat 1 2 = (1 / 2 : ℚ) := by norm_num
        simp only [hm, ofCoeffList_cons, ofCoeffList_nil, map_neg, map_one]
        linear_combination X * hhalf⟩,
    RowTable.ofMatrix_toMatrix (by decide)⟩

end

end CslibFrontierTests.CoeffListRowTable
