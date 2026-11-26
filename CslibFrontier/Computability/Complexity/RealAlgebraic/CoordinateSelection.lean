/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.WordCoordinateFingerprintLabels
public import CslibFrontier.Foundations.Analysis.MvPolynomial.CoordinateCriticalLimit
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledIndexedFeasibility
import Mathlib.Tactic.NormNum

/-!
# Indexed constraints for coordinate selection

Row zero tests the source polynomial. The next rows test membership in the coordinate
root grid. The strict inequalities are the coordinate fingerprint labels from the shared
witness word. These constraints express the selection conditions without a counting-level
increase for the individual row queries.

Their sum-of-squares feasibility polynomial uses one auxiliary variable per label.
Its modular evaluator costs one additional counting level over the labels.
A fixed-width witness can make the labels select any given point in the root grid.

Adapted from lean-canny's `SelectionSystem` and `SelectionSystemCorrectness` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

/-- The source equation at row zero followed by the coordinate root equations.
Positive addresses read the preceding coordinate address. -/
noncomputable def selectionEquation {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) (j : ℕ) : MvPolynomial (Fin n) ℤ :=
  if decide (j = 0) then F else indexedCoordinateEquation F hF hn (j - 1)

/-- Row zero is the source polynomial. -/
@[simp] theorem selectionEquation_zero {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) : selectionEquation F hF hn 0 = F := by
  simp [selectionEquation]

/-- Evaluate the source or a coordinate equation selected by a binary row address at
counting level `a + 18`. All rows share polynomial-time bounds independent of the row address. -/
noncomputable def Controlled.selectionEquations {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat) :
    Controlled (fun q : α × ℕ => selectionEquation (F q.1) (hF q.1) (hn q.1) q.2)
      (encPair enc encNat) (a + 18) := by
  have hw := fst enc encNat
  have hj := snd enc encNat
  let CI := (C.indexedCoordinateEquations E hn hdpos hF hd).preprocess
    (fun q : α × ℕ => (q.1, q.2 - 1)) (hw.prod (binary_sub' hj (.const 1)))
  let C₀ := (C.preprocess (fun q : α × ℕ => q.1) hw).mono (Nat.le_add_right a 18)
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0))
      (encPair enc encNat) encBool := by
    simpa only [Nat.le_zero_eq] using binary_le' hj (.const 0)
  exact C₀.ite CI (fun q => decide (q.2 = 0)) hguard

/-- The selection equations share the degree bound, norm exponent and prime cutoff at row zero.
These instance bounds apply to every binary row address. -/
theorem Controlled.selectionEquations_bounds_eq {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (w : α) (j : ℕ) :
    let equations := C.selectionEquations E hn hdpos hF hd
    equations.degreeBound (w, j) = equations.degreeBound (w, 0) ∧
      equations.massExponent (w, j) = equations.massExponent (w, 0) ∧
      equations.cutoff (w, j) = equations.cutoff (w, 0) := by
  obtain ⟨hD, hb, hc⟩ := C.indexedCoordinateEquations_bounds_eq E hn hdpos hF hd w (j - 1)
  simp only [selectionEquations, degreeBound_ite, massExponent_ite, cutoff_ite, mono, preprocess,
    Function.comp_apply, Nat.zero_sub, hD, hb, hc, eq_self, and_self]

/-- The indexed rows express that the point is a source zero in the coordinate root grid
and that every coordinate satisfies the fingerprint label from the shared word. -/
theorem selection_constraints_iff {n d : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (mass : ℕ) (hn : 0 < n) (word : List Bool) (x : Fin n → ℝ) :
    ((∀ j < n + 1, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionEquation F hF hn j) = 0) ∧
      ∀ j < n, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x
        (wordCoordinateFingerprintTest F hF mass hn word j)) ↔
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x F = 0 ∧
        x ∈ coordinateRootGrid (Nat.succ_pos d) F hF ∧
        ∀ i : Fin n, 0 < (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
          (Int.castRingHom ℝ) (x i) := by
  have hrow (i : Fin n) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x (selectionEquation F hF hn (i.val + 1)) =
        (Polynomial.Bivariate.swap
          (parametricCoordinatePolynomial (Nat.succ_pos d) F hF i)).leadingCoeff.eval₂
          (Int.castRingHom ℝ) (x i) := by
    simpa only [selectionEquation, decide_eq_true_eq, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel, Nat.mod_eq_of_lt i.isLt] using
      eval₂_indexedCoordinateEquation (Int.castRingHom ℝ) F hF hn x i.val
  have hlabel (i : Fin n) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x
        (wordCoordinateFingerprintTest F hF mass hn word i.val) =
        (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
          (Int.castRingHom ℝ) (x i) := by
    simpa only [Nat.mod_eq_of_lt i.isLt] using
      eval₂_wordCoordinateFingerprintTest (Int.castRingHom ℝ) F hF mass hn word x i.val
  simp only [mem_coordinateRootGrid, Polynomial.IsRoot.def, Polynomial.eval_map]
  constructor
  · rintro ⟨heq, hpos⟩
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · simpa only [selectionEquation_zero] using heq 0 (Nat.zero_lt_succ n)
    · exact (hrow i).symm.trans (heq (i.val + 1) (Nat.succ_lt_succ i.isLt))
    · simpa only [hlabel i] using hpos i.val i.isLt
  · rintro ⟨hzero, hgrid, hpos⟩
    constructor
    · intro j hj
      cases j with
      | zero => simpa only [selectionEquation_zero] using hzero
      | succ j =>
        let i : Fin n := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
        exact (hrow i).trans (hgrid i)
    · intro j hj
      rw [hlabel (⟨j, hj⟩ : Fin n)]
      exact hpos ⟨j, hj⟩

/-- The feasibility polynomial for a source equation, its coordinate root grid and the
fingerprint constraints supplied by a shared word. The last `n` coordinates are auxiliary. -/
noncomputable def selectionFeasibilityPolynomial {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (mass : ℕ)
    (hn : 0 < n) (word : List Bool) : MvPolynomial (Fin (n + n)) ℤ :=
  indexedFeasibilityPolynomial (selectionEquation F hF hn)
    (wordCoordinateFingerprintTest F hF mass hn word) (n + 1) n

/-- Assemble the coordinate-selection feasibility polynomial at counting level `a + 21`.
The degree, norm and prime bounds for each row family are computed at address zero. -/
noncomputable def Controlled.selectionFeasibility {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun w => selectionFeasibilityPolynomial (F w) (hF w) (C.massExponent w)
      (hn w) (word w)) enc (a + 21) := by
  let CP := (C.selectionEquations E hn hdpos hF hd).mono
    (Nat.add_le_add_left (by decide : 18 ≤ 20) a)
  let CQ := C.wordCoordinateFingerprintTests E hn hdpos hF hd word hword
  have hrowZero : ComputableInPolyTime (fun w : α => (w, (0 : ℕ))) enc (encPair enc encNat) :=
    id'.prod (.const 0)
  have hP (w j) := C.selectionEquations_bounds_eq E hn hdpos hF hd w j
  have hQ (w j) := C.wordCoordinateFingerprintTests_bounds_eq E hn hdpos hF hd word hword w j
  exact CP.indexedFeasibility CQ E (fun w => n w + 1) n
    (fun w => max (CP.degreeBound (w, 0)) (CQ.degreeBound (w, 0)))
    (fun w => max (CP.massExponent (w, 0)) (CQ.massExponent (w, 0)))
    (fun w => max (CP.cutoff (w, 0)) (CQ.cutoff (w, 0)))
    (binary_add' (unary_to_binary.comp C.arity_computable) (.const 1)) C.arity_computable
    (binary_max' (CP.degree_computable.comp hrowZero) (CQ.degree_computable.comp hrowZero))
    (binary_max' (CP.mass_computable.comp hrowZero) (CQ.mass_computable.comp hrowZero))
    (binary_max' (CP.cutoff_computable.comp hrowZero) (CQ.cutoff_computable.comp hrowZero))
    (fun w j _ => (CP.degree_le (w, j)).trans ((hP w j).1.le.trans (le_max_left _ _)))
    (fun w j _ => (CQ.degree_le (w, j)).trans ((hQ w j).1.le.trans (le_max_right _ _)))
    (fun w j _ => by
      obtain ⟨_, hb, _⟩ := hP w j
      exact (CP.mass_le (w, j)).trans
        (Nat.pow_le_pow_right (by decide) (hb.le.trans (le_max_left _ _))))
    (fun w j _ => by
      obtain ⟨_, hb, _⟩ := hQ w j
      exact (CQ.mass_le (w, j)).trans
        (Nat.pow_le_pow_right (by decide) (hb.le.trans (le_max_right _ _))))
    (fun w j _ => by
      obtain ⟨_, _, hc⟩ := hP w j
      exact hc.le.trans (le_max_left _ _))
    (fun w j _ => by
      obtain ⟨_, _, hc⟩ := hQ w j
      exact hc.le.trans (le_max_right _ _))

/-- The selection feasibility polynomial has a real zero exactly when a source zero
in the coordinate root grid satisfies all fingerprint tests supplied by the word. -/
theorem exists_selectionFeasibilityPolynomial_zero_iff {n d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (mass : ℕ)
    (hn : 0 < n) (word : List Bool) :
    (∃ z : Fin (n + n) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z
      (selectionFeasibilityPolynomial F hF mass hn word) = 0) ↔
    ∃ x : Fin n → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) x F = 0 ∧
      x ∈ coordinateRootGrid (Nat.succ_pos d) F hF ∧
      ∀ i : Fin n, 0 < (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
        (Int.castRingHom ℝ) (x i) := by
  rw [selectionFeasibilityPolynomial, exists_indexedFeasibilityPolynomial_zero_iff]
  exact exists_congr (selection_constraints_iff F hF mass hn word)

open Classical in
/-- Each coordinate root grid point has a fixed-width word whose fingerprint labels
select precisely that point in the grid. This adapts lean-canny's
`CoordinateFingerprintSelection` and `ChoiceTupleCompleteness`
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. -/
theorem exists_coordinateSelectionWitness {n d mass : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hmass : F.coeffNorm1 ≤ 2 ^ mass) (hd : 1 ≤ d) (hn : 0 < n)
    {x : Fin n → ℝ} (hx : x ∈ coordinateRootGrid (Nat.succ_pos d) F hF) :
    ∃ word : List Bool, word.length = coordinateFingerprintWitnessWidth ((d + 1) ^ n) n ∧
      ∀ y : Fin n → ℝ, (y ∈ coordinateRootGrid (Nat.succ_pos d) F hF ∧
        ∀ i : Fin n, 0 < (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
          (Int.castRingHom ℝ) (y i)) ↔ y = x := by
  let D := (d + 1) ^ n
  let b := parametricCoordinateCoeffNormExponent n (d + 1) mass
  let Q (i : Fin n) :=
    (Polynomial.Bivariate.swap
      (parametricCoordinatePolynomial (Nat.succ_pos d) F hF i)).leadingCoeff
  have hroot {y : Fin n → ℝ} (hy : y ∈ coordinateRootGrid (Nat.succ_pos d) F hF) (i : Fin n) :
      (Q i).eval₂ (Int.castRingHom ℝ) (y i) = 0 := by
    simpa only [Q, Polynomial.IsRoot.def, Polynomial.eval_map] using mem_coordinateRootGrid.mp hy i
  have hbounds (i : Fin n) :=
    leadingCoeff_swap_parametricCoordinatePolynomial_bounds (Nat.succ_le_succ hd) F hF hmass i
  have hone : (1 : Polynomial ℤ).coeffNorm1 ≤ 2 ^ b := by
    rw [Polynomial.coeffNorm1_one]
    exact Nat.one_le_two_pow
  have hlabels (i : Fin n) := Polynomial.exists_fingerprintIntegerRootLabel (q := 1)
    (leadingCoeff_swap_parametricCoordinatePolynomial_ne_zero (Nat.succ_pos d) F hF i)
    (hbounds i).1 (by simp) (hbounds i).2 hone (hroot hx i) (by simp)
  choose μ t target hprime hmin hmax ht htarget hpos hneg using hlabels
  let f (i : Fin n) : CoordinateFingerprint := ⟨μ i, t i, target i⟩
  have hf (i : Fin n) : (f i).Bounded D := ⟨hmin i, hmax i, ht i, htarget i⟩
  obtain ⟨word, hlen, hword⟩ := exists_coordinateFingerprintWitness f hf
  have hlabel (i : Fin n) : wordCoordinateFingerprintLabel F hF mass hn word i.val =
      Polynomial.fingerprintIntegerRootLabel (Q i) 1 D b (μ i) (t i) (target i) := by
    simp only [wordCoordinateFingerprintLabel, hword i, Nat.mod_eq_of_lt i.isLt, f, Q, D, b]
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨word, hlen, fun y => ?_⟩
  constructor
  · rintro ⟨hy, hypos⟩
    funext i
    by_contra hne
    have hnpos := (hneg i (y i) (hroot hy i) hne).trans (by norm_num : (-1 : ℝ) / 2 ≤ 0)
    exact (not_lt_of_ge hnpos) (by simpa only [hlabel] using hypos i)
  · rintro rfl
    refine ⟨hx, fun i => ?_⟩
    rw [hlabel i]
    exact hhalf.trans_le (hpos i)

end Cslib.Complexity.RealAlgebraic
