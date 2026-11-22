/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.VOLE.KOSExtractor
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Probability.HashFamily.Polynomial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Ordinary-module clients and edge-case audits for `VOLE.KOSExtractor`

1. **Zero, one, and two-opening edge cases:** exercises `kosExtract_nil`,
   `kosExtract_singleton_of_eq`, `not_hasKOSBadTriple_of_length_le_two`, and
   `kosExtract_eval_eq_of_not_hasKOSBadTriple` without unfolding `kosExtract`, plus exact zero
   failure measure (`0.choose 3 = 1.choose 3 = 2.choose 3 = 0`).
2. **Nontrivial 4-opening collinear recovery and 3-opening failure witness over `ZMod 5`:** uses
   `KOSLine.eq_of_eval_eq` and `kosAffineDefect_eq_zero_of_eval_eq` through the public interface to
   verify exact recovery of a 4-point VOLE line and explicit extraction of a nonzero affine defect
   via `kosFailureWitness` under a colliding seed, alongside the `1 / 5` probability bound.
3. **Concrete characteristic-two `BinaryField 4` (`GF(16)`) client:** instantiates
   `toOuterMeasure_kosExtract_graph_failure_le` with FAEST's fixed-length Horner polynomial hash
   `coeffPolyHashLinear` (`isUniversalHash_coeffPolyHash`), proving the concrete bound
   `((n - 1 : ℝ≥0∞) / 16) * (responses.length.choose 3)`.
-/

public section

namespace CslibFrontierTests.Crypto.VOLEKOSExtractor

open Cslib Cslib.Probability Cslib.Crypto.Protocols.VOLE
open scoped ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Linear inner-product hash `(s₀, s₁) ↦ (v ↦ s₀ * v₀ + s₁ * v₁)` over `ZMod 5`. -/
private def dotHash (s : Fin 2 → ZMod 5) : (Fin 2 → ZMod 5) →ₗ[ZMod 5] ZMod 5 where
  toFun v := s 0 * v 0 + s 1 * v 1
  map_add' x y := by
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem isUniversalHash_dotHash :
    IsUniversalHash (PMF.uniformOfFintype (Fin 2 → ZMod 5))
      (fun s v => dotHash s v) ((1 : ℝ≥0∞) / 5) := by
  have hbound : ((5 : ℕ) : ℝ≥0∞) / Fintype.card (Fin 2 → ZMod 5) = (1 : ℝ≥0∞) / 5 := by
    rw [show Fintype.card (Fin 2 → ZMod 5) = 25 by decide, Nat.cast_ofNat, Nat.cast_ofNat]
    exact (ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
      (by norm_num)
  rw [← hbound]
  refine IsUniversalHash.of_card_le fun x y hxy => ?_
  revert x y
  decide

/-! ## 1. Zero, one, and two-opening edge cases -/

-- Zero openings return `⟨0, 0⟩` via `kosExtract_nil`.
example :
    kosExtract (dotHash ![1, 0]) ([] : List (ZMod 5 × (Fin 2 → ZMod 5))) ⟨1, 2⟩ = ⟨0, 0⟩ :=
  kosExtract_nil _ _

-- One accepted opening returns the constant line `⟨0, q₀⟩`, which evaluates to `q₀` at `Δ₀`.
example :
    let q₀ : Fin 2 → ZMod 5 := ![3, 4]
    let line := kosExtract (dotHash ![1, 0]) [((2 : ZMod 5), q₀)] ⟨0, 3⟩
    line = ⟨0, q₀⟩ ∧ line.eval (2 : ZMod 5) = q₀ := by
  refine ⟨kosExtract_singleton_of_eq (by decide), ?_⟩
  rw [kosExtract_singleton_of_eq (by decide)]
  decide

-- Deterministic two-opening guarantee: on any response graph of length ≤ 2, every accepted opening
-- lies on `kosExtract` unconditionally (`not_hasKOSBadTriple_of_length_le_two`).
example (s : Fin 2 → ZMod 5) {responses : List (ZMod 5 × (Fin 2 → ZMod 5))}
    (hgraph : IsResponseGraph responses) (hlen : responses.length ≤ 2)
    (target : KOSLine (ZMod 5)) {p : ZMod 5 × (Fin 2 → ZMod 5)}
    (hp : p ∈ responses) (hhash : dotHash s p.2 = target.eval p.1) :
    (kosExtract (dotHash s) responses target).eval p.1 = p.2 :=
  kosExtract_eval_eq_of_not_hasKOSBadTriple (dotHash s) hgraph
    (not_hasKOSBadTriple_of_length_le_two (dotHash s) hlen) target hp hhash

-- On any response graph of length ≤ 2, `toOuterMeasure_kosExtract_graph_failure_le` gives exact
-- failure measure `0`.
example {responses : List (ZMod 5 × (Fin 2 → ZMod 5))}
    (hgraph : IsResponseGraph responses) (hlen : responses.length ≤ 2) :
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
      {s | ∃ (target : KOSLine (ZMod 5)) (p : ZMod 5 × (Fin 2 → ZMod 5)),
        p ∈ responses ∧ dotHash s p.2 = target.eval p.1 ∧
          (kosExtract (dotHash s) responses target).eval p.1 ≠ p.2} = 0 := by
  have hchoose : responses.length.choose 3 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hle := toOuterMeasure_kosExtract_graph_failure_le isUniversalHash_dotHash hgraph
  rw [hchoose, Nat.cast_zero, mul_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

/-! ## 2. Nontrivial 4-opening collinear client and 3-opening failure witness -/

private def sampleSlope : Fin 2 → ZMod 5 := ![2, 3]
private def sampleIntercept : Fin 2 → ZMod 5 := ![1, 4]

private def collinearFour : List (ZMod 5 × (Fin 2 → ZMod 5)) :=
  [(0, ![1, 4]), (1, ![3, 2]), (2, ![0, 0]), (3, ![2, 3])]

-- All four openings lie on `⟨sampleSlope, sampleIntercept⟩` (so every triple has zero defect and
-- `¬ HasKOSBadTriple` holds), and `KOSLine.eq_of_eval_eq` recovers the exact VOLE line without
-- unfolding `kosExtract`.
example :
    let s : Fin 2 → ZMod 5 := ![1, 1]
    let target : KOSLine (ZMod 5) := ⟨dotHash s sampleSlope, dotHash s sampleIntercept⟩
    kosExtract (dotHash s) collinearFour target = ⟨sampleSlope, sampleIntercept⟩ ∧
      ∀ p ∈ collinearFour, (kosExtract (dotHash s) collinearFour target).eval p.1 = p.2 := by
  dsimp only
  have hgraph : IsResponseGraph collinearFour := IsResponseGraph.of_nodup_fst (by decide)
  have honLine : ∀ p ∈ collinearFour,
      (⟨sampleSlope, sampleIntercept⟩ : KOSLine (Fin 2 → ZMod 5)).eval p.1 = p.2 := by
    intro p hp
    fin_cases hp <;> ext i <;> fin_cases i <;>
      simp only [KOSLine.eval, sampleSlope, sampleIntercept, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      decide
  have hnobad : ¬ HasKOSBadTriple (dotHash ![1, 1]) collinearFour := by
    rintro ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, _, _, _, hdef, _⟩
    exact hdef (kosAffineDefect_eq_zero_of_eval_eq
      (honLine p₀ hp₀) (honLine p₁ hp₁) (honLine p₂ hp₂))
  have heval : ∀ p ∈ collinearFour,
      (kosExtract (dotHash ![1, 1]) collinearFour
        ⟨dotHash ![1, 1] sampleSlope, dotHash ![1, 1] sampleIntercept⟩).eval p.1 = p.2 := by
    intro p hp
    refine kosExtract_eval_eq_of_not_hasKOSBadTriple (dotHash ![1, 1]) hgraph hnobad _ hp ?_
    have hp_line := congrArg (dotHash ![1, 1]) (honLine p hp).symm
    simpa [KOSLine.eval, map_add, map_smul] using hp_line
  refine ⟨KOSLine.eq_of_eval_eq (Δ₀ := (0 : ZMod 5)) (Δ₁ := (1 : ZMod 5)) (by decide) ?_ ?_, heval⟩
  · exact (heval (0, ![1, 4]) (by decide)).trans (honLine (0, ![1, 4]) (by decide)).symm
  · exact (heval (1, ![3, 2]) (by decide)).trans (honLine (1, ![3, 2]) (by decide)).symm

/-- Non-collinear 3-opening response graph `[(0, (0, 0)), (1, (1, 0)), (2, (0, 1))]`. -/
def nonCollinearThree : List (ZMod 5 × (Fin 2 → ZMod 5)) :=
  [(0, ![0, 0]), (1, ![1, 0]), (2, ![0, 1])]

theorem isResponseGraph_nonCollinearThree : IsResponseGraph nonCollinearThree :=
  IsResponseGraph.of_nodup_fst (by decide)

-- Under colliding seed `s = ![1, 2]`, all three openings hash onto `target = ⟨1, 0⟩`, yet their
-- `kosAffineDefect` is nonzero (`![4, 1] ≠ 0`), so `kosExtract` cannot evaluate to all three
-- openings (`kosAffineDefect_eq_zero_of_eval_eq`) and `kosFailureWitness` extracts a nonzero defect
-- in `ker (dotHash ![1, 2])` without unfolding `kosExtract`.
example :
    let s : Fin 2 → ZMod 5 := ![1, 2]
    let target : KOSLine (ZMod 5) := ⟨1, 0⟩
    ∃ (p : ZMod 5 × (Fin 2 → ZMod 5)) (hp : p ∈ nonCollinearThree)
      (hhash : dotHash s p.2 = target.eval p.1)
      (hfail : (kosExtract (dotHash s) nonCollinearThree target).eval p.1 ≠ p.2),
      let w := kosFailureWitness (dotHash s) isResponseGraph_nonCollinearThree hp hhash hfail
      kosAffineDefect w.p₀ w.p₁ w.p₂ ≠ 0 ∧ dotHash s (kosAffineDefect w.p₀ w.p₁ w.p₂) = 0 := by
  dsimp only
  let p₀ : ZMod 5 × (Fin 2 → ZMod 5) := (0, ![0, 0])
  let p₁ : ZMod 5 × (Fin 2 → ZMod 5) := (1, ![1, 0])
  let p₂ : ZMod 5 × (Fin 2 → ZMod 5) := (2, ![0, 1])
  have hdef_ne : kosAffineDefect p₀ p₁ p₂ ≠ 0 := by
    intro h0
    have h1 := congrFun h0 1
    revert h1
    simp only [kosAffineDefect, p₀, p₁, p₂, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    decide
  let line := kosExtract (dotHash ![1, 2]) nonCollinearThree ⟨1, 0⟩
  by_cases hf₀ : line.eval p₀.1 = p₀.2
  · by_cases hf₁ : line.eval p₁.1 = p₁.2
    · have hf₂ : line.eval p₂.1 ≠ p₂.2 := fun hf₂ =>
        hdef_ne (kosAffineDefect_eq_zero_of_eval_eq hf₀ hf₁ hf₂)
      refine ⟨p₂, by decide, by decide, hf₂, ?_⟩
      let w := kosFailureWitness (dotHash ![1, 2]) isResponseGraph_nonCollinearThree
        (p := p₂) (by decide) (by decide) hf₂
      exact ⟨w.defect_ne_zero, w.map_defect_eq_zero⟩
    · refine ⟨p₁, by decide, by decide, hf₁, ?_⟩
      let w := kosFailureWitness (dotHash ![1, 2]) isResponseGraph_nonCollinearThree
        (p := p₁) (by decide) (by decide) hf₁
      exact ⟨w.defect_ne_zero, w.map_defect_eq_zero⟩
  · refine ⟨p₀, by decide, by decide, hf₀, ?_⟩
    let w := kosFailureWitness (dotHash ![1, 2]) isResponseGraph_nonCollinearThree
      (p := p₀) (by decide) (by decide) hf₀
    exact ⟨w.defect_ne_zero, w.map_defect_eq_zero⟩

-- Over a uniform seed, extraction on `nonCollinearThree` (`|S| = 3`, `choose 3 3 = 1`) fails with
-- probability at most `1 / 5`.
example :
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
      {s | ∃ (target : KOSLine (ZMod 5)) (p : ZMod 5 × (Fin 2 → ZMod 5)),
        p ∈ nonCollinearThree ∧ dotHash s p.2 = target.eval p.1 ∧
          (kosExtract (dotHash s) nonCollinearThree target).eval p.1 ≠ p.2} ≤ (1 : ℝ≥0∞) / 5 := by
  simpa [nonCollinearThree] using
    toOuterMeasure_kosExtract_graph_failure_le isUniversalHash_dotHash
      isResponseGraph_nonCollinearThree

/-! ## 3. Concrete characteristic-two `BinaryField 4` (`GF(16)`) polynomial-hash client -/

/-- Concrete characteristic-two instantiation over `BinaryField 4` (`GF(16)`) using FAEST §4.2.1's
Horner polynomial hash `coeffPolyHashLinear`: on any response graph `responses` of width-`n` vectors
over `GF(16)`, KOS affine extraction fails with probability at most
`((n - 1 : ℝ≥0∞) / 16) * (responses.length.choose 3)`. -/
theorem binaryField_coeffPolyHash_kos_bound (n : ℕ)
    {responses : List (BinaryField 4 × (Fin n → BinaryField 4))}
    (hgraph : IsResponseGraph responses) :
    (PMF.uniformOfFintype (BinaryField 4)).toOuterMeasure
      {k | ∃ (target : KOSLine (BinaryField 4)) (p : BinaryField 4 × (Fin n → BinaryField 4)),
        p ∈ responses ∧ coeffPolyHashLinear k n p.2 = target.eval p.1 ∧
          (kosExtract (coeffPolyHashLinear k n) responses target).eval p.1 ≠ p.2} ≤
      ((↑(n - 1) : ℝ≥0∞) / 16) * (responses.length.choose 3 : ℝ≥0∞) := by
  have hcard : (Fintype.card (BinaryField 4) : ℝ≥0∞) = 16 := by
    exact_mod_cast BinaryField.card (w := 4) (by decide)
  rw [← hcard]
  exact toOuterMeasure_kosExtract_graph_failure_le
    (H := fun k => coeffPolyHashLinear k n) (isUniversalHash_coeffPolyHash n) hgraph

end CslibFrontierTests.Crypto.VOLEKOSExtractor
