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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
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
A second system adds counterexample variables and one equation at the same counting level.
The counterexample renaming places the parameters before the witnesses and leaves room
for the leading reciprocal variable of the parameter system.

Adapted from lean-canny's `SelectionSystem`, `SelectionSystemCorrectness`,
`SelectionCounterexampleSystem`, `SelectionCounterexampleCorrectness` and
`CounterexampleVariableOrder` at
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

private noncomputable def indexedFeasibilityOfUniformRows {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P Q : (q : α × ℕ) → MvPolynomial (Fin (n q.1)) ℤ}
    (CP : Controlled P (encPair enc encNat) a) (CQ : Controlled Q (encPair enc encNat) a)
    (E : Decoder enc) (e k : α → ℕ)
    (he : ComputableInPolyTime e enc encNat) (hk : ComputableInPolyTime k enc encUnary)
    (hP : ∀ w j, CP.degreeBound (w, j) = CP.degreeBound (w, 0) ∧
      CP.massExponent (w, j) = CP.massExponent (w, 0) ∧ CP.cutoff (w, j) = CP.cutoff (w, 0))
    (hQ : ∀ w j, CQ.degreeBound (w, j) = CQ.degreeBound (w, 0) ∧
      CQ.massExponent (w, j) = CQ.massExponent (w, 0) ∧ CQ.cutoff (w, j) = CQ.cutoff (w, 0)) :
    Controlled (fun w => indexedFeasibilityPolynomial (fun j => P (w, j)) (fun j => Q (w, j))
      (e w) (k w)) enc (a + 1) := by
  have hrowZero : ComputableInPolyTime (fun w : α => (w, (0 : ℕ))) enc (encPair enc encNat) :=
    id'.prod (.const 0)
  exact CP.indexedFeasibility CQ E e k
    (fun w => max (CP.degreeBound (w, 0)) (CQ.degreeBound (w, 0)))
    (fun w => max (CP.massExponent (w, 0)) (CQ.massExponent (w, 0)))
    (fun w => max (CP.cutoff (w, 0)) (CQ.cutoff (w, 0)))
    he hk
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
  exact indexedFeasibilityOfUniformRows CP CQ E (fun w => n w + 1) n
    (binary_add' (unary_to_binary.comp C.arity_computable) (.const 1)) C.arity_computable
    (C.selectionEquations_bounds_eq E hn hdpos hF hd)
    (C.wordCoordinateFingerprintTests_bounds_eq E hn hdpos hF hd word hword)

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

private noncomputable def selectionCounterexampleEquation {n u d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (R : MvPolynomial (Fin (n + u)) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hn : 0 < n) (j : ℕ) : MvPolynomial (Fin (n + u)) ℤ :=
  if decide (j = 0) then R else
    MvPolynomial.rename (Fin.castAdd u) (selectionEquation F hF hn (j - 1))

/-- Feasibility of a selected source zero together with a zero of the counterexample
equation `R`. The coordinates are the selected point, the extra variables, then the
auxiliary variables for the fingerprint labels. -/
noncomputable def selectionCounterexamplePolynomial {n u d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (R : MvPolynomial (Fin (n + u)) ℤ)
    (hF : F.totalDegree ≤ d + 1) (mass : ℕ) (hn : 0 < n) (word : List Bool) :
    MvPolynomial (Fin ((n + u) + n)) ℤ :=
  indexedFeasibilityPolynomial (selectionCounterexampleEquation F R hF hn)
    (fun j => MvPolynomial.rename (Fin.castAdd u)
      (wordCoordinateFingerprintTest F hF mass hn word j)) (n + 2) n

/-- Assemble the selected counterexample system at counting level `a + 21` when the
extra equation is controlled at level `a + 20` and the extra arity is unary-polytime. -/
noncomputable def Controlled.selectionCounterexample {α : Type} {n u : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    {R : (w : α) → MvPolynomial (Fin (n w + u w)) ℤ}
    (C : Controlled F enc a) (CR : Controlled R enc (a + 20))
    (hu : ComputableInPolyTime u enc encUnary) (E : Decoder enc) {d : α → ℕ}
    (hn : ∀ w, 0 < n w) (hdpos : ∀ w, 1 ≤ d w)
    (hF : ∀ w, (F w).totalDegree ≤ d w + 1) (hd : ComputableInPolyTime d enc encNat)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun w => selectionCounterexamplePolynomial (F w) (R w) (hF w)
      (C.massExponent w) (hn w) (word w)) enc (a + 21) := by
  have hw := fst enc encNat
  have hj := snd enc encNat
  let equations := (C.selectionEquations E hn hdpos hF hd).mono
    (Nat.add_le_add_left (by decide : 18 ≤ 20) a)
  let shifted := (equations.appendVariables (fun q => u q.1) (hu.comp hw)).preprocess
    (fun q : α × ℕ => (q.1, q.2 - 1)) (hw.prod (binary_sub' hj (.const 1)))
  let labels := (C.wordCoordinateFingerprintTests E hn hdpos hF hd word hword).appendVariables
    (fun q => u q.1) (hu.comp hw)
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0))
      (encPair enc encNat) encBool := by
    simpa only [Nat.le_zero_eq] using binary_le' hj (.const 0)
  let rows := (CR.preprocess (fun q : α × ℕ => q.1) hw).ite shifted
    (fun q => decide (q.2 = 0)) hguard
  refine indexedFeasibilityOfUniformRows (n := fun w => n w + u w) rows labels E
    (fun w => n w + 2) n
    (binary_add' (unary_to_binary.comp C.arity_computable) (.const 2)) C.arity_computable ?_ ?_
  · intro w j
    obtain ⟨hD, hb, hc⟩ := C.selectionEquations_bounds_eq E hn hdpos hF hd w (j - 1)
    simp only [rows, degreeBound_ite, massExponent_ite, cutoff_ite, shifted, preprocess,
      Function.comp_apply, degreeBound_appendVariables, massExponent_appendVariables,
      cutoff_appendVariables, equations, mono, Nat.zero_sub, hD, hb, hc, eq_self, and_self]
  · intro w j
    simpa only [labels, degreeBound_appendVariables, massExponent_appendVariables,
      cutoff_appendVariables] using C.wordCoordinateFingerprintTests_bounds_eq E hn hdpos
        hF hd word hword w j

/-- The counterexample system has a real zero exactly when some selected source zero
extends to a zero of the extra equation. -/
theorem exists_selectionCounterexamplePolynomial_zero_iff {n u d : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (R : MvPolynomial (Fin (n + u)) ℤ)
    (hF : F.totalDegree ≤ d + 1) (mass : ℕ) (hn : 0 < n) (word : List Bool) :
    (∃ z : Fin ((n + u) + n) → ℝ, MvPolynomial.eval₂ (Int.castRingHom ℝ) z
      (selectionCounterexamplePolynomial F R hF mass hn word) = 0) ↔
    ∃ x : Fin n → ℝ, ∃ y : Fin u → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) x F = 0 ∧
      x ∈ coordinateRootGrid (Nat.succ_pos d) F hF ∧
      (∀ i : Fin n, 0 < (wordCoordinateFingerprintLabel F hF mass hn word i.val).eval₂
        (Int.castRingHom ℝ) (x i)) ∧
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x y) R = 0 := by
  rw [selectionCounterexamplePolynomial, exists_indexedFeasibilityPolynomial_zero_iff]
  have hrename (x : Fin n → ℝ) (y : Fin u → ℝ) (P : MvPolynomial (Fin n) ℤ) :
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x y)
        (MvPolynomial.rename (Fin.castAdd u) P) = MvPolynomial.eval₂ (Int.castRingHom ℝ) x P := by
    simp only [MvPolynomial.eval₂_rename, Function.comp_def, Fin.addCases_left]
  constructor
  · rintro ⟨z, heq, hpos⟩
    let x (i : Fin n) := z (i.castAdd u)
    let y (i : Fin u) := z (i.natAdd n)
    have hz : Fin.addCases x y = z := funext (Fin.addCases_castAdd_natAdd z)
    rw [← hz] at heq hpos
    obtain ⟨hFzero, hgrid, hlabels⟩ := (selection_constraints_iff F hF mass hn word x).mp
      ⟨fun j hj => by
        simpa only [selectionCounterexampleEquation, decide_eq_true_eq, Nat.succ_ne_zero,
          ite_false, Nat.add_sub_cancel, hrename] using heq (j + 1) (Nat.succ_lt_succ hj),
        fun j hj => by simpa only [hrename] using hpos j hj⟩
    refine ⟨x, y, hFzero, hgrid, hlabels, ?_⟩
    simpa only [selectionCounterexampleEquation, decide_true, ite_true] using heq 0 (by omega)
  · rintro ⟨x, y, hFzero, hgrid, hlabels, hR⟩
    obtain ⟨heq, hpos⟩ :=
      (selection_constraints_iff F hF mass hn word x).mpr ⟨hFzero, hgrid, hlabels⟩
    refine ⟨Fin.addCases x y, fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero =>
        simpa only [selectionCounterexampleEquation, decide_true, ite_true] using hR
      | succ j =>
        simpa only [selectionCounterexampleEquation, decide_eq_true_eq, Nat.succ_ne_zero,
          ite_false, Nat.add_sub_cancel, hrename] using heq j (Nat.lt_of_succ_lt_succ hj)
    · simpa only [hrename] using hpos j hj

private def counterexampleVariable {n m : ℕ} : Fin (n + m) → Fin ((m + 1) + n) :=
  Fin.addCases (Fin.natAdd (m + 1)) (fun i : Fin m => Fin.castAdd n i.succ)

/-- Reorder a polynomial from witness-then-parameter coordinates to parameter-then-witness
coordinates, with an unused leading slot for the reciprocal variable. -/
noncomputable def counterexamplePolynomial {n m : ℕ} (P : MvPolynomial (Fin (n + m)) ℤ) :
    MvPolynomial (Fin ((m + 1) + n)) ℤ :=
  MvPolynomial.rename counterexampleVariable P

/-- The first entry of the parameter block is ignored. Evaluation uses the remaining
parameters and the full witness block in their original order. -/
theorem eval₂_counterexamplePolynomial {n m : ℕ} {S : Type*} [CommRing S] (f : ℤ →+* S)
    (P : MvPolynomial (Fin (n + m)) ℤ) (c : Fin (m + 1) → S) (z : Fin n → S) :
    MvPolynomial.eval₂ f (Fin.addCases c z) (counterexamplePolynomial P) =
      MvPolynomial.eval₂ f (Fin.addCases z (fun i => c i.succ)) P := by
  rw [counterexamplePolynomial, MvPolynomial.eval₂_rename]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_def, counterexampleVariable, Fin.addCases_left, Fin.addCases_right]

private def counterexampleAddress (n m i : ℕ) : ℕ :=
  if i < n then m + 1 + i else i - n + 1

private def counterexamplePoint (n m : ℕ) (z : List ℕ) : List ℕ :=
  (List.range (n + m)).map (fun i => z.getD (counterexampleAddress n m i) 0)

/-- Reorder the counterexample equation without increasing its counting level.
Both block sizes are computed in unary, and absent entries of the evaluation point
continue to be read as zero. -/
noncomputable def Controlled.counterexampleOrder {α : Type} {n m : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}
    (C : Controlled P enc a) (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => counterexamplePolynomial (P w)) enc a := by
  let input := encPair enc (encList encNat)
  have hw := fst enc (encList encNat)
  have hz := snd enc (encList encNat)
  have hinput := fst input encUnary
  have hi := unary_to_binary.comp (snd input encUnary)
  have hn' := (unary_to_binary.comp hn).comp (hw.comp hinput)
  have hm' := (unary_to_binary.comp hm).comp (hw.comp hinput)
  have haddress : ComputableInPolyTime
      (fun q : (α × List ℕ) × ℕ =>
        let ((w, _), i) := q
        counterexampleAddress (n w) (m w) i)
      (encPair input encUnary) encNat := by
    exact ite_decide (binary_lt' hi hn') (binary_add' (binary_add' hm' (.const 1)) hi)
      (binary_add' (binary_sub' hi hn') (.const 1))
  have hpoint : ComputableInPolyTime
      (fun q : α × List ℕ => counterexamplePoint (n q.1) (m q.1) q.2) input (encList encNat) :=
    mapWithInput (range.comp (C.arity_computable.comp hw))
      (listGetD_binary 0 (hz.comp hinput) haddress)
  apply C.rename (unary_add' (unary_add' hm (.const 1)) hn)
    (fun _ => counterexampleVariable) _ hpoint
  intro w z i
  rw [List.getD_eq_getElem?_getD, counterexamplePoint, List.getElem?_map,
    List.getElem?_range i.isLt]
  change z.getD (counterexampleAddress (n w) (m w) i.val) 0 = z.getD _ 0
  congr 1
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [counterexampleAddress, Fin.val_castAdd, j.isLt, ite_true, counterexampleVariable,
      Fin.addCases_left, Fin.val_natAdd]
  · simp only [counterexampleAddress, Fin.val_natAdd,
      Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left,
      counterexampleVariable, Fin.addCases_right, Fin.val_castAdd, Fin.val_succ]

end Cslib.Complexity.RealAlgebraic
