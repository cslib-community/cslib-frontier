/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Combinatorics.RectangleFreeMatrix
import CslibFrontier.Foundations.Combinatorics.BrownMatrix
import CslibFrontier.Computability.Circuit.Rectifier.Basic
import CslibFrontier.Computability.Circuit.Rectifier.ComplementSeparation

register_result "nechiporuk-rectifier-k-free-lower-bound" where
  title := "Every rectifier circuit for a K-free Boolean matrix A has at least |A| / (K - 1)² \
    edges, and OR(A) = OR_d(A) = |A| when A is 2-free"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2014ORComplement,
      theorem := "Nechiporuk's K-free rectifier bound and 2-free identity (quoted)",
      locator := "p. 1, l. 31 and p. 3, proof of Lemma 3" },
    { paper := Nechiporuk1970, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.RectifierCircuit.Computes.boolMatrixWeight_le_sq_pred_mul_size,
    Cslib.Circuits.boolMatrixWeight_le_sq_pred_mul_orComplexity,
    Cslib.Circuits.orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two,
    Cslib.Circuits.orDepthComplexity_eq_boolMatrixWeight_of_isRectangleFree_two
  ]
  scope := "Unconditional over arbitrary finite row/column types [Fintype α] [Fintype β] and all \
    K : ℕ in the general directed-graph rectifier model with disjoint injective input and output \
    poles (requiring neither acyclicity nor source/sink degree restrictions for the lower bound). \
    Proves the sharper factor (K - 1)² in |A| ≤ (K - 1)² · OR(A) rather than Sergeev's quoted K², \
    yielding the exact identity OR(A) = OR_d(A) = |A| (for all 1 ≤ d) at K = 2. Nechiporuk1970 is \
    cited through Sergeev2014ORComplement and was not inspected directly."

register_result "sergeev-two-rectangle-count-and-lift" where
  title := "Dense m × m Boolean matrices contain Ω((|A| / m)⁴) 2-rectangles, and the C(m, 2) × \
    C(m, 2) 2-rectangle lift of a k-free matrix is (C(k - 1, 2) + 1)-free"
  topic := "combinatorics"
  sources := [
    { paper := Sergeev2014ORComplement,
      theorem := "Lemma 1 and Lemma 2",
      locator := "p. 2" }
  ]
  theorems := [
    Cslib.pow_four_boolMatrixWeight_le_mul_boolMatrixWeight_twoRectMatrix,
    Cslib.IsRectangleFreeMatrix.twoRectMatrix
  ]
  scope := "Unconditional over arbitrary finite index types: Lemma 1 states |A| ≥ 2 m^{3/2} \
    without truncation as 4 * |α|^3 ≤ |A|^2 and proves the exact integer lower bound \
    |A|^4 ≤ 32 * |α|^4 * |twoRectMatrix A|; Lemma 2 holds over arbitrary rectangular index types \
    α, β and all k : ℕ, correcting the p. 2 line-above-Lemma-2 misprint 'in B' to 'in A'."

register_result "brown-k33-free-unit-sphere-matrix" where
  title := "Brown's unit-sphere matrix over (ℤ/pℤ)³ (p ≡ 3 mod 4 prime) is 3-rectangle-free with \
    exact weight p⁴(p - 1)"
  topic := "combinatorics"
  sources := [
    { paper := Sergeev2014ORComplement,
      theorem := "Brown's 3-free m × m matrix of weight Θ(m^{5/3}) \
        (used in proof of Theorem 1(ii))",
      locator := "p. 3, l. 120" },
    { paper := Brown1966, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.card_row_brownMatrix,
    Cslib.boolMatrixWeight_brownMatrix,
    Cslib.isRectangleFreeMatrix_brownMatrix
  ]
  scope := "Unconditional for every prime p with p % 4 = 3 ([Fact p.Prime]), over V = Fin 3 → \
    ZMod p of cardinality m = p³. Proves exact uniform row weight p(p - 1), exact total weight \
    p⁴(p - 1), and 3-rectangle-freeness (absence of 3 × 3 all-ones submatrices). Brown1966 is \
    cited through Sergeev2014ORComplement and was not inspected directly."

register_result "sergeev-or-complexity-complement-separation" where
  title := "Explicit n × n Boolean matrices C with OR₃(C) = O(n), 2-free complement C̄, and \
    OR(C̄) = |C̄| = Ω(n^{4/3})"
  topic := "circuit complexity"
  sources := [
    { paper := Sergeev2014ORComplement,
      theorem := "Lemma 3 and Theorem 1(ii)",
      locator := "pp. 1–3" },
    { paper := Brown1966, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.orDepthComplexity_three_compl_twoRectMatrix_le,
    Cslib.Circuits.orDepthComplexity_three_compl_twoRectMatrix_le_seven_mul,
    Cslib.Circuits.pow_four_boolMatrixWeight_le_mul_orComplexity_twoRectMatrix,
    Cslib.Circuits.pow_four_boolMatrixWeight_le_eight_mul_orComplexity_twoRectMatrix,
    Cslib.Circuits.orDepthComplexity_three_sergeevComplementMatrix_le,
    Cslib.Circuits.orComplexity_sergeevComplementMatrix_le,
    Cslib.Circuits.isRectangleFreeMatrix_compl_sergeevComplementMatrix,
    Cslib.Circuits.orComplexity_compl_sergeevComplementMatrix_eq_boolMatrixWeight,
    Cslib.Circuits.choose_pow_four_le_mul_orComplexity_compl_sergeevComplementMatrix_pow_three,
    Cslib.Circuits.exists_gt_sergeev_or_complement_separation
  ]
  scope := "Lemma 3 proves OR₃(B̄) ≤ 4 C(m, 2) + |Ā| ≤ 7 C(m, 2) (for 3 ≤ m) via the explicit \
    4-layer circuit complTwoRectCircuit and proves |A|⁴ ≤ 32 C(k - 1, 2)² m⁴ OR(B) ≤ \
    8 (k m)⁴ OR(B) when A is k-free and 4 m³ ≤ |A|² (correcting the printed variable slip \
    (|A| / (k n))⁴ on pp. 2–3 to (|A| / (k m))⁴). Theorem 1(ii) instantiates C = \
    sergeevComplementMatrix p of dimension n = C(p³, 2) for every prime p ≡ 3 (mod 4), proving \
    OR(C) ≤ OR₃(C) ≤ 7 n, C̄ is 2-free, OR(C̄) = |C̄|, and n⁴ ≤ 2²³ OR(C̄)³, together with an \
    unbounded Fin n × Fin n family via Dirichlet's theorem. Theorem 1(i)'s projective norm-graph \
    instantiation (KollarRonyaiSzabo1996) is outside this entry (#7622)."
