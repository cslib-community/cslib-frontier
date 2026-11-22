/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Determinant.Projection
import CslibFrontier.Computability.Circuit.Arithmetic.DeterminantalComplexity

register_result "determinant-formula-simulation" where
  title := "Valiant: arithmetic formulas compute projections of linear-size determinants"
  topic := "algebraic complexity"
  sources := [
    { paper := OrzelSrinivasanTavenasYehudayoff2025,
      theorem := "Lemma 4 (determinant part, with Definition 1)",
      locator := "LIPIcs FSTTCS 2025, §1.2 pp. 47:3–47:4 and §2 pp. 47:5–47:6" },
    { paper := Saptharishi2026Survey,
      theorem := "Theorem thm:vp and Section sec:formula-to-dets",
      locator := "chap_vpvnp.tex (Chapter \"Algebraic complexity classes\"), rev. af95c539" },
    { paper := Valiant1979Algebra,
      theorem := "Theorem 1",
      locator := "STOC '79, §1–§2, pp. 249–251" }
  ]
  theorems := [
    Cslib.Circuits.Formula.isProjection_det,
    Cslib.Circuits.Formula.isProjection_det_toCircuit,
    Cslib.Circuits.Formula.determinantalComplexity_eval_le,
    Cslib.Circuits.Formula.determinantalComplexity_toCircuit_le
  ]
  scope := "Over every commutative ring K, the formal polynomial computed by any arithmetic \
    formula F : Formula (arithSignature K) n (with Formula.size counting addition, \
    multiplication and constant nodes and input leaves free, whereas Valiant §1–§2 states \
    |P_i| + 2 over a field counting binary operations) is a plain variable-and-scalar \
    projection (IsProjection, with no outer scalar multiplier) of (genericMatrix K \
    (F.size + 1)).det, and hence has determinantal complexity at most F.size + 1 without field, \
    characteristic or nontriviality hypotheses. Proved via the strictly upper-triangular \
    specialization branching program IsSubstABP and the (N - 1) minor identity (avoiding the \
    parallel-edge issue in Valiant's original addition step noted and corrected in §1.2 and §2.1 \
    of Grenet–Kaltofen–Koiran–Portier 2012, whose digraph proof recovers Liu and Regan's 2006 \
    e + 1 bound for green-size-e formulas with at least one addition over char ≠ 2). No uniform \
    machine runtime is claimed."

register_result "valiant-determinant-projection-universality" where
  title := "Valiant's projection universality: every multivariate polynomial is a projection of \
    a generic determinant"
  topic := "algebraic complexity"
  sources := [
    { paper := Saptharishi2026Survey,
      theorem := "Theorem thm:vp",
      locator := "chap_vpvnp.tex (Chapter \"Algebraic complexity classes\"), rev. af95c539" },
    { paper := OrzelSrinivasanTavenasYehudayoff2025,
      theorem := "Lemma 4 (determinant part) and §2 dc(f) < ∞ remark",
      locator := "LIPIcs FSTTCS 2025, §1.2 p. 47:4 and §2 p. 47:6" },
    { paper := Valiant1979Algebra,
      theorem := "Theorem 1",
      locator := "STOC '79, §1–§2, pp. 249–251" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_isProjection_det
  ]
  scope := "Over every commutative ring K and arbitrary variable index type σ (without \
    finiteness or decidable-equality hypotheses on σ and without nontriviality on K, whereas \
    Valiant §1–§2 works over a field in F[x_1, …, x_i]), every f : MvPolynomial σ K is a plain \
    variable-and-scalar projection (IsProjection, with no outer scalar multiplier) of \
    (genericMatrix K m).det for some m : ℕ."

register_result "valiant-determinantal-universality" where
  title := "Valiant's universality: every multivariate polynomial has finite determinantal \
    complexity"
  topic := "algebraic complexity"
  sources := [
    { paper := Saptharishi2026Survey,
      theorem := "Chapter chap:dc (via Theorem thm:vp)",
      locator := "chap_dc.tex and chap_vpvnp.tex, rev. af95c539" },
    { paper := OrzelSrinivasanTavenasYehudayoff2025,
      theorem := "Lemma 4 (determinant part) and §2 dc(f) < ∞ remark",
      locator := "LIPIcs FSTTCS 2025, §1.2 p. 47:4 and §2 p. 47:6" },
    { paper := Valiant1979Algebra,
      theorem := "Theorem 1",
      locator := "STOC '79, §1–§2, pp. 249–251" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_hasDeterminantalRepresentation,
    Cslib.Circuits.Arithmetic.determinantalComplexity_lt_top,
    Cslib.Circuits.Arithmetic.exists_hasDeterminantalRepresentation_eq_determinantalComplexity
  ]
  scope := "Over every commutative ring K and arbitrary variable index type σ (without \
    finiteness or decidable-equality hypotheses on σ and without nontriviality on K), every \
    f : MvPolynomial σ K admits a finite determinantal representation, has \
    determinantalComplexity f < ⊤, and attains determinantalComplexity f at some finite \
    matrix dimension. HasDeterminantalRepresentation and determinantalComplexity formalize \
    Saptharishi's (chap_dc.tex) affine-linear entry definition, which is upper-bounded by the \
    projection-based determinantal complexity dc(f) of Orzel et al. (§2 p. 47:6)."
