/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.SignLabelEvaluation
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
import CslibFrontier.Computability.Complexity.RealAlgebraic.RootLabelPrecision
import CslibFrontier.Computability.Complexity.RealAlgebraic.SparseDerivativeTestEvaluation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Modular evaluation of the sparse integer root label

Binary degree and coefficient norm bounds determine the shared dyadic precision. The
qualifying value, binary derivative orders and addressed coefficients supply the test
values for the cleared sign label. Only the number of tests uses a unary encoding.

Adapted from `SparseRootLabelEvaluation` and `NativeRootLabelBounds` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier precision and score formulas.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Evaluate the sparse root label from the qualifying residue, addressed source coefficients,
binary derivative orders and addressed target residues. The qualifying test is included in
addition to the `N` derivative slots. -/
noncomputable def sparseRootLabelResidue (p D N b z base : ℕ)
    (c : ℕ → ℕ) (orders : List ℕ) (target : ℕ → ℕ) : ℕ :=
  signLabelResidue p (Polynomial.derivativeRootLabelPrecision D b) (N + 1)
    (sparseDerivativeTestResidue p D z base c orders) target

/-- The uniform sparse evaluator has level `F_(max a 3 + 4)` for coefficient access at
level `F_a`, with the qualifying value available at the derivative evaluator's level. -/
theorem sparseRootLabelResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D N b z base : α → ℕ} {orders : α → List ℕ} {c target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hN : ComputableInPolyTime N enc encUnary)
    (hb : ComputableInPolyTime b enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hbase : base ∈ CountingFunction (max a 3 + 1) enc encNat)
    (horders : ComputableInPolyTime orders enc (encList encNat))
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat)
    (ht : target ∈ CountingFunction (max a 3 + 4) (encPair enc encNat) encNat) :
    (fun w => sparseRootLabelResidue (p w) (D w) (N w) (b w) (z w) (base w)
      (fun j => c (w, j)) (orders w) (fun j => target (w, j))) ∈
        CountingFunction (max a 3 + 4) enc encNat := by
  have hwidth : ComputableInPolyTime (fun w => N w + 1) enc encUnary := unary_succ.comp hN
  have hvalue := sparseDerivativeTestResidue_mem E hp hD hz hbase horders hc
  have ht' : target ∈ CountingFunction (max a 3 + 1 + 3) (encPair enc encNat) encNat := by
    simpa only [Nat.add_assoc] using ht
  simpa only [sparseRootLabelResidue, Nat.add_assoc] using
    signLabelResidue_mem E hp (derivativeRootLabelPrecision_polyTime hD hb) hwidth hvalue ht'

/-- The native evaluator agrees with the sparse integer label in the determinant criterion
when the inputs supply the addressed coefficients and signs modulo a prime greater than the
degree bound. The qualifying value may come from a separate evaluator. -/
theorem sparseRootLabelResidue_cast {p D N : ℕ} [Fact p.Prime]
    (q b₀ : Polynomial ℤ) (b z base : ℕ) (c target : ℕ → ℕ)
    (L : List (Fin D × SignType)) (hD : q.natDegree ≤ D) (hprime : D < p)
    (hc : ∀ j ≤ D, (c j : ZMod p) = (q.map (Int.castRingHom (ZMod p))).coeff j)
    (hbase : (base : ZMod p) = b₀.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p))
    (ht : ∀ i : Fin (N + 1), (target i.val : ZMod p) =
      (((Polynomial.sparseRootLabelTests q b₀ N L i).2 : ℤ) : ZMod p)) :
    (sparseRootLabelResidue p D N b z base c (L.map (fun t => t.1.val + 1)) target : ZMod p) =
      (Polynomial.sparseIntegerRootLabel q b₀ N b L).eval₂
        (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  rw [sparseRootLabelResidue, Polynomial.sparseIntegerRootLabel]
  exact signLabelResidue_cast _ _ _ _ _ _
    (fun i => sparseDerivativeTestResidue_cast q b₀ z base c L hD hprime hc hbase i) ht

end Cslib.Complexity.RealAlgebraic
