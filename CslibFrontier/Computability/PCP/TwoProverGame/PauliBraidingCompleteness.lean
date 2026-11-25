/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.PauliBraidingAnticommutation
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Basic
import CslibFrontier.Foundations.Quantum.Algebra.FourierMeasurement
import CslibFrontier.Foundations.Quantum.Algebra.Involution
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import CslibFrontier.Foundations.Quantum.PauliTwirl

/-!
# Honest play in the CHSH Pauli braiding verifier

In a basis round, each prover uses the joint character measurement of the
corresponding Pauli family and reports the two requested parities. In the
anticommutation round the first role measures a sum or difference of two
anticommuting Pauli observables and the second role measures one of the Pauli
observables. The special consistency round uses the same second-role observable.

The maximally entangled state's diagonal support in either common basis gives agreement on
the shared parity, including when the sorted queries have repeated strings. Trace evaluation
at an odd pair yields the optimal CHSH correlation in both physical role assignments.

The verifier is the CHSH specialization of [Natarajan and Vidick, Figure 2][NatarajanVidick2017]
(arXiv:1610.03574v1, §4.1).

## Main definitions

* `Cslib.PCP.pauliBraidingHonestStrategy`: the strategy on the maximally entangled state.

## Main results

* `Cslib.PCP.quantumWinProb_pauliBraidingHonestStrategy`: the strategy attains
  `(2 + cos (π / 8) ^ 2) / 3`.
* `Cslib.PCP.quantumWinProb_pauliBraidingGame_le`: no finite-dimensional tensor strategy
  has a higher score.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.PCP

open Finset Quantum BitString Matrix
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator Real

variable {n : ℕ}

private abbrev PauliMatrix (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev BraidingAnswer := (Bool × Bool) ⊕ Bool

private noncomputable def honestPauli (basis : Bool) (x : Fin n → Bool) : PauliMatrix n :=
  cond basis (pauliZPow x) (pauliXPow x)

private theorem honestPauli_isHermitian (basis : Bool) (x : Fin n → Bool) :
    (honestPauli basis x).IsHermitian := by
  cases basis
  · exact pauliXPow_isHermitian x
  · exact pauliZPow_isHermitian x

private theorem honestPauli_mul_self (basis : Bool) (x : Fin n → Bool) :
    honestPauli basis x * honestPauli basis x = 1 := by
  cases basis
  · exact pauliXPow_mul_self x
  · exact pauliZPow_mul_self x

private theorem honestPauli_mul (basis : Bool) (x y : Fin n → Bool) :
    honestPauli basis x * honestPauli basis y = honestPauli basis (x + y) := by
  cases basis
  · exact pauliXPow_mul x y
  · exact pauliZPow_mul x y

private noncomputable def honestBasisMeasurement (basis : Bool) :
    Measurement (Fin n → Bool) (PauliMatrix n) :=
  fourierMeasurement (honestPauli basis)
    (fun x => (honestPauli_isHermitian basis x).isSelfAdjoint) (honestPauli_mul_self basis)

private theorem honestBasisMeasurement_projective (basis : Bool) :
    (honestBasisMeasurement (n := n) basis).IsProjective :=
  fourierMeasurement_isProjective_of_linear _ _ (honestPauli_mul basis)

private theorem honestBasisMeasurement_charObs (basis : Bool) (x : Fin n → Bool) :
    (honestBasisMeasurement basis).charObs x = honestPauli basis x :=
  walshSum_fourierMeasurement_of_linear _ _ (honestPauli_mul basis) x

private theorem transpose_honestPauli (basis : Bool) (a : Fin n → Bool) :
    (honestPauli basis a)ᵀ = honestPauli basis a := by
  ext x y
  change honestPauli basis a y x = honestPauli basis a x y
  cases basis
  · change pauliXPow a y x = pauliXPow a x y
    simp only [pauliXPow_apply]
    refine if_congr ?_ rfl rfl
    constructor <;> intro h <;> rw [h, BitString.add_cancel_right]
  · change pauliZPow a y x = pauliZPow a x y
    by_cases h : x = y
    · subst y
      rfl
    · rw [pauliZPow_apply, pauliZPow_apply, ite_eq_right (Ne.symm h), ite_eq_right h]

private theorem transpose_honestBasisMeasurement_effect (basis : Bool) (u : Fin n → Bool) :
    ((honestBasisMeasurement basis).effect u)ᵀ = (honestBasisMeasurement basis).effect u := by
  rw [honestBasisMeasurement, fourierMeasurement_effect,
    fourierCoeff_mul_self_of_linear _ (honestPauli_mul basis)]
  simp only [fourierCoeff, walshSum, transpose_smul, transpose_sum, transpose_honestPauli]

private theorem odd_pauli_anticommute (p : ↥(oddPairs (Fin n))) :
    pauliZPow p.val.2 * pauliXPow p.val.1 = -(pauliXPow p.val.1 * pauliZPow p.val.2) := by
  rw [pauliZPow_mul_pauliXPow, mem_oddPairs.mp p.property, signVal_true,
    Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul]

private noncomputable def honestCHSHObservable
    (secondRole question : Bool) (p : ↥(oddPairs (Fin n))) : PauliMatrix n :=
  if secondRole then honestPauli question (if question then p.val.2 else p.val.1)
  else ((√2 / 2 : ℝ) : ℂ) •
    (if question then pauliXPow p.val.1 - pauliZPow p.val.2
      else pauliXPow p.val.1 + pauliZPow p.val.2)

private theorem honestCHSHObservable_isHermitian
    (secondRole question : Bool) (p : ↥(oddPairs (Fin n))) :
    (honestCHSHObservable secondRole question p).IsHermitian := by
  cases secondRole
  · have hc : IsSelfAdjoint ((√2 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
    cases question
    · exact ((pauliXPow_isHermitian _).add (pauliZPow_isHermitian _)).smul hc
    · exact ((pauliXPow_isHermitian _).sub (pauliZPow_isHermitian _)).smul hc
  · exact honestPauli_isHermitian _ _

private theorem honestCHSHObservable_mul_self
    (secondRole question : Bool) (p : ↥(oddPairs (Fin n))) :
    honestCHSHObservable secondRole question p * honestCHSHObservable secondRole question p =
      1 := by
  cases secondRole
  · have h := normalized_add_sub_mul_self_of_anticommute (pauliXPow_mul_self p.val.1)
      (pauliZPow_mul_self p.val.2) (odd_pauli_anticommute p) question
    cases question <;> exact h
  · exact honestPauli_mul_self _ _

private noncomputable def honestCHSHMeasurement
    (role b : Bool) (p : ↥(oddPairs (Fin n))) : POVM Bool (Fin n → Bool) :=
  if role then ((honestBasisMeasurement b).map
      ((if b then p.val.2 else p.val.1) ⬝ᵥ ·)).toPOVM
  else POVM.ofObservable (honestCHSHObservable role b p)
    (honestCHSHObservable_isHermitian role b p) (honestCHSHObservable_mul_self role b p)

private theorem honestCHSHMeasurement_observable (role b : Bool) (p : ↥(oddPairs (Fin n))) :
    (honestCHSHMeasurement role b p).observable = honestCHSHObservable role b p := by
  cases role
  · simp only [honestCHSHMeasurement, Bool.false_eq_true, ite_false,
      POVM.observable_ofObservable]
  · change ((honestBasisMeasurement b).map
      ((if b then p.val.2 else p.val.1) ⬝ᵥ ·)).observable =
      honestPauli b (if b then p.val.2 else p.val.1)
    rw [← Measurement.charObs_eq_observable_map, honestBasisMeasurement_charObs]

private def basisAnswer (q : (Fin n → Bool) × (Fin n → Bool)) (u : Fin n → Bool) :
    BraidingAnswer :=
  .inl (q.1 ⬝ᵥ u, q.2 ⬝ᵥ u)

private noncomputable def honestMeasurement (q : PauliBraidingQuestion n Bool) :
    Measurement BraidingAnswer (PauliMatrix n) :=
  match q with
  | .basis basis strings => (honestBasisMeasurement basis).map (basisAnswer strings)
  | .anticommutation role b p =>
    (honestCHSHMeasurement role b p).toMeasurement.map Sum.inr

/-- The honest strategy uses the maximally entangled state of the two bit-string
registers. Each player applies the same measurement rule to its tagged question. -/
noncomputable def pauliBraidingHonestStrategy (n : ℕ) :
    QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) (Fin n → Bool) (Fin n → Bool) where
  state := maxEntangled (Fin n → Bool)
  norm_state := norm_maxEntangled
  alice q := (honestMeasurement q).toPOVM
  bob q := (honestMeasurement q).toPOVM

/-- The honest basis measurements are projective. -/
theorem isProjective_pauliBraidingHonestStrategy_basis (basis : Bool)
    (q : (Fin n → Bool) × (Fin n → Bool)) :
    ((pauliBraidingHonestStrategy n).alice (.basis basis q)).toMeasurement.IsProjective ∧
    ((pauliBraidingHonestStrategy n).bob (.basis basis q)).toMeasurement.IsProjective :=
  ⟨(honestBasisMeasurement_projective basis).map _, (honestBasisMeasurement_projective basis).map _⟩

private noncomputable def basisStrategy (n : ℕ) :
    QuantumStrategy Bool Bool (Fin n → Bool) (Fin n → Bool) (Fin n → Bool) (Fin n → Bool) where
  state := maxEntangled (Fin n → Bool)
  norm_state := norm_maxEntangled
  alice basis := (honestBasisMeasurement basis).toPOVM
  bob basis := (honestBasisMeasurement basis).toPOVM

private theorem basisStrategy_prob_eq_zero_of_ne (basis : Bool) {u v : Fin n → Bool}
    (h : u ≠ v) : (basisStrategy n).toCommuting.prob basis basis u v = 0 := by
  rw [QuantumStrategy.prob_toCommuting, QuantumStrategy.prob_eq]
  let X := (honestBasisMeasurement basis).effect u
  let Y := (honestBasisMeasurement basis).effect v
  change (star (maxEntangled (Fin n → Bool)).ofLp ⬝ᵥ
    ((X ⊗ₖ Y) *ᵥ (maxEntangled (Fin n → Bool)).ofLp)).re = 0
  rw [star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace,
    transpose_honestBasisMeasurement_effect,
    (honestBasisMeasurement_projective basis).mul_eq_zero h]
  simp

private theorem sum_ite_prob_honest_mapped
    (basis basis' : Bool) (q r : PauliBraidingQuestion n Bool)
    (f g : (Fin n → Bool) → BraidingAnswer)
    (hf : honestMeasurement q = (honestBasisMeasurement basis).map f)
    (hg : honestMeasurement r = (honestBasisMeasurement basis').map g)
    (accepts : BraidingAnswer → BraidingAnswer → Prop) [∀ a b, Decidable (accepts a b)]
    (h : ∀ u v, (basisStrategy n).toCommuting.prob basis basis' u v ≠ 0 → accepts (f u) (g v)) :
    let S := (pauliBraidingHonestStrategy n).toCommuting
    (∑ a, ∑ b, if accepts a b then S.prob q r a b else 0) = 1 := by
  intro S
  let K := (basisStrategy n).toCommuting
  let L := K.map (fun _ : Unit => basis) (fun _ : Unit => basis') (fun _ => f) (fun _ => g)
  have hprob (a b : BraidingAnswer) :
      S.prob q r a b = L.prob () () a b := by
    change (K.state (kroneckerOne ((honestMeasurement q).effect a) *
      oneKronecker ((honestMeasurement r).effect b))).re =
      (K.state (((K.alice basis).map f).effect a * ((K.bob basis').map g).effect b)).re
    simp only [hf, hg, Measurement.map_effect, map_sum]
    rfl
  simp only [hprob]
  rw [K.sum_ite_prob_map]
  refine Eq.trans (sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_) (K.sum_prob basis basis')
  by_cases huv : K.prob basis basis' u v = 0
  · rw [huv, ite_self]
  · rw [ite_eq_left (h u v huv)]

private theorem sum_ite_prob_honest_sameBasis
    (basis : Bool) (q r : PauliBraidingQuestion n Bool) (f g : (Fin n → Bool) → BraidingAnswer)
    (hf : honestMeasurement q = (honestBasisMeasurement basis).map f)
    (hg : honestMeasurement r = (honestBasisMeasurement basis).map g)
    (accepts : BraidingAnswer → BraidingAnswer → Prop) [∀ a b, Decidable (accepts a b)]
    (h : ∀ u, accepts (f u) (g u)) :
    let S := (pauliBraidingHonestStrategy n).toCommuting
    (∑ a, ∑ b, if accepts a b then S.prob q r a b else 0) = 1 := by
  apply sum_ite_prob_honest_mapped basis basis q r f g hf hg accepts
  intro u v huv
  obtain rfl := not_imp_comm.1 (basisStrategy_prob_eq_zero_of_ne basis) huv
  exact h u

private theorem honest_prob_swap (q r : PauliBraidingQuestion n Bool) (a b : BraidingAnswer) :
    let S := (pauliBraidingHonestStrategy n).toCommuting
    S.prob q r a b = S.prob r q b a := by
  intro S
  rw [QuantumStrategy.prob_toCommuting, QuantumStrategy.prob_toCommuting,
    QuantumStrategy.prob_eq, QuantumStrategy.prob_eq]
  let X := (honestMeasurement q).effect a
  let Y := (honestMeasurement r).effect b
  let ψ := maxEntangled (Fin n → Bool)
  change (star ψ.ofLp ⬝ᵥ ((X ⊗ₖ Y) *ᵥ ψ.ofLp)).re =
    (star ψ.ofLp ⬝ᵥ ((Y ⊗ₖ X) *ᵥ ψ.ofLp)).re
  rw [star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace,
    star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace, ← trace_transpose (Xᵀ * Y),
    transpose_mul, transpose_transpose]


section Linearity

variable [Nonempty (Fin n)]

private noncomputable def linearityWithBasis (n : ℕ) [Nonempty (Fin n)] (basis : Bool) :
    SeededGame (SymmetricLinearitySeed n) (PauliBraidingQuestion n Bool)
      (PauliBraidingQuestion n Bool) BraidingAnswer BraidingAnswer :=
  (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).pullbackSeed
    (symmetricLinearityGame n).seed (.linearity basis)

private theorem honest_linearityWithBasis (basis : Bool) :
    (linearityWithBasis n basis).commutingWinProb
      (pauliBraidingHonestStrategy n).toCommuting = 1 := by
  classical
  rw [SeededGame.commutingWinProb_eq_expect_of_uniform (linearityWithBasis n basis) rfl]
  refine (expect_congr rfl fun s _ => ?_).trans (Fintype.expect_const _)
  let q := (symmetricLinearityGame n).query s
  change (∑ a, ∑ b, if (linearityWithBasis n basis).accepts s a b then
    (pauliBraidingHonestStrategy n).toCommuting.prob (.basis basis q.1) (.basis basis q.2) a b
      else 0) = 1
  apply sum_ite_prob_honest_sameBasis basis _ _ (basisAnswer q.1) (basisAnswer q.2) rfl rfl
  intro u
  let f : (Fin n → Bool) →+ Bool :=
    { toFun := fun x => x ⬝ᵥ u
      map_zero' := zero_dotProduct _
      map_add' := fun a b => add_dotProduct a b u }
  exact symmetricLinearityGame_accepts_linear s f

/-- The honest strategy passes the linearity branch with probability one. -/
theorem quantumWinProb_pauliBraidingHonestStrategy_linearity :
    (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 0).quantumWinProb
      (pauliBraidingHonestStrategy n) = 1 := by
  let game := pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)
  let S := (pauliBraidingHonestStrategy n).toCommuting
  let law (b : Bool) : PMF (PauliBraidingSeed n Bool) :=
    (symmetricLinearityGame n).seed.map (PauliBraidingSeed.linearity b)
  rw [← SeededGame.commutingWinProb_toCommuting]
  change ({ game with seed := (Probability.PMF.uniformOfFintype Bool).bind law }).answersWinProb
    S.answers = 1
  rw [SeededGame.answersWinProb_bind_uniformSeed]
  refine (expect_congr rfl fun b _ => ?_).trans (Fintype.expect_const _)
  have he := game.answersWinProb_pullbackSeed (symmetricLinearityGame n).seed
    (PauliBraidingSeed.linearity b) S.answers
  exact he.symm.trans (honest_linearityWithBasis b)

end Linearity

section CHSH

private noncomputable def honestCHSHStrategy (p : ↥(oddPairs (Fin n))) :
    QuantumStrategy Bool Bool Bool Bool (Fin n → Bool) (Fin n → Bool) where
  state := maxEntangled (Fin n → Bool)
  norm_state := norm_maxEntangled
  alice b := honestCHSHMeasurement false b p
  bob b := honestCHSHMeasurement true b p

private theorem correlation_honestCHSHStrategy (p : ↥(oddPairs (Fin n))) (x y : Bool) :
    (honestCHSHStrategy p).correlation x y =
      if x && y then -(√2 / 2) else √2 / 2 := by
  let X := pauliXPow p.val.1
  let Z := pauliZPow p.val.2
  have hXt : Xᵀ = X := transpose_honestPauli false _
  have hZt : Zᵀ = Z := transpose_honestPauli true _
  have hXZ : trace (X * Z) = 0 := by
    have ht : trace (Z * X) = -trace (X * Z) := by
      rw [show Z * X = -(X * Z) from odd_pauli_anticommute p, trace_neg]
    rw [trace_mul_comm] at ht
    linear_combination ht / 2
  have hZX : trace (Z * X) = 0 := (trace_mul_comm _ _).trans hXZ
  have hN : (Fintype.card (Fin n → Bool) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha (r : Bool) : ((honestCHSHStrategy p).alice r).observable =
      honestCHSHObservable false r p :=
    honestCHSHMeasurement_observable _ _ _
  have hb (r : Bool) : ((honestCHSHStrategy p).bob r).observable =
      honestCHSHObservable true r p :=
    honestCHSHMeasurement_observable true r p
  rw [QuantumStrategy.correlation, ha, hb]
  change (star (maxEntangled (Fin n → Bool)).ofLp ⬝ᵥ
    ((honestCHSHObservable false x p ⊗ₖ honestCHSHObservable true y p) *ᵥ
      (maxEntangled (Fin n → Bool)).ofLp)).re = _
  rw [star_maxEntangled_dotProduct_kronecker_mulVec_eq_trace]
  cases x <;> cases y <;>
    simp only [honestCHSHObservable, Bool.false_eq_true, ite_true, ite_false, honestPauli,
      Bool.cond_false, Bool.cond_true, transpose_smul, transpose_add, transpose_sub,
      ← show X = pauliXPow p.val.1 from rfl, ← show Z = pauliZPow p.val.2 from rfl,
      hXt, hZt, smul_mul_assoc, add_mul, sub_mul, show X * X = 1 from pauliXPow_mul_self _,
      show Z * Z = 1 from pauliZPow_mul_self _, trace_smul, trace_add, trace_sub, trace_one,
      hXZ, hZX, add_zero, zero_add, sub_zero, zero_sub, smul_eq_mul, mul_neg, neg_div,
      mul_div_cancel_right₀ _ hN, Complex.ofReal_re, Complex.neg_re, Bool.and_true,
      Bool.and_false, eq_self]

private theorem quantumWinProb_honestCHSHStrategy (p : ↥(oddPairs (Fin n))) :
    TwoProverGame.chsh.quantumWinProb (honestCHSHStrategy p) = Real.cos (π / 8) ^ 2 := by
  rw [TwoProverGame.quantumWinProb_chsh, Real.cos_sq_pi_div_eight]
  simp only [correlation_honestCHSHStrategy, Bool.and_true, Bool.and_false,
    Bool.false_eq_true, ite_true, ite_false]
  ring

variable [Nonempty (Fin n)]

private theorem honest_pauliBraidingCHSHGame
    (p : ↥(oddPairs (Fin n))) (roles : Bool) :
    (pauliBraidingCHSHGame n roles p).commutingWinProb
      (pauliBraidingHonestStrategy n).toCommuting = Real.cos (π / 8) ^ 2 := by
  classical
  let S := (pauliBraidingHonestStrategy n).toCommuting
  let K := (honestCHSHStrategy p).toCommuting
  let L := K.map id id (fun _ => Sum.inr (α := Bool × Bool)) (fun _ => Sum.inr (α := Bool × Bool))
  let g := pauliBraidingCHSHGame n roles p
  have hK (x y : Bool) (a b : BraidingAnswer) :
      S.prob (.anticommutation false x p) (.anticommutation true y p) a b = L.prob x y a b := by
    change (K.state (kroneckerOne ((honestMeasurement (.anticommutation false x p)).effect a) *
      oneKronecker ((honestMeasurement (.anticommutation true y p)).effect b))).re =
      (K.state (((K.alice x).map Sum.inr).effect a * ((K.bob y).map Sum.inr).effect b)).re
    simp only [honestMeasurement, Measurement.map_effect, map_sum]
    rfl
  have hperm (x y : Bool) (a b : BraidingAnswer) :
      S.prob (g.query (x, y)).1 (g.query (x, y)).2 (cond roles b a) (cond roles a b) =
        L.prob x y a b := by
    cases roles
    · exact hK x y a b
    · change S.prob (.anticommutation true y p) (.anticommutation false x p) b a = _
      rw [honest_prob_swap]
      exact hK x y a b
  rw [← quantumWinProb_honestCHSHStrategy p, ← TwoProverGame.commutingWinProb_toCommuting]
  change g.commutingWinProb S = TwoProverGame.chsh.toSeeded.commutingWinProb K
  rw [SeededGame.commutingWinProb_eq_sum, SeededGame.commutingWinProb_eq_sum]
  refine sum_congr rfl fun ⟨x, y⟩ _ =>
    congrArg ((TwoProverGame.chsh.questions (x, y)).toReal * ·) ?_
  have hswap :
      (∑ a, ∑ b, if g.accepts (x, y) a b then S.prob (g.query (x, y)).1 (g.query (x, y)).2 a b
        else 0) =
      ∑ a, ∑ b, if g.accepts (x, y) (cond roles b a) (cond roles a b) then L.prob x y a b
        else 0 := by
    simp only [← hperm]
    cases roles
    · rfl
    · exact sum_comm
  rw [hswap, K.sum_ite_prob_map]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => if_congr ?_ rfl rfl
  cases roles <;> rfl

/-- The honest strategy attains the CHSH value in the anticommutation branch. -/
theorem quantumWinProb_pauliBraidingHonestStrategy_anticommutation :
    (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 1).quantumWinProb
      (pauliBraidingHonestStrategy n) = Real.cos (π / 8) ^ 2 := by
  rw [← SeededGame.commutingWinProb_toCommuting,
    commutingWinProb_pauliBraidingAnticommutation_eq_expect]
  let := oddPairs_nonempty (ι := Fin n)
  simp only [honest_pauliBraidingCHSHGame, Fintype.expect_const]

end CHSH

section Consistency

variable [Nonempty (Fin n)]

private theorem honest_sameBasis_accepts (roles basis : Bool) (p : ↥(oddPairs (Fin n)))
    (dummy : Fin n → Bool) :
    let game := pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)
    let s := PauliBraidingSeed.sameBasis roles basis p dummy
    let S := (pauliBraidingHonestStrategy n).toCommuting
    letI : ∀ a b, Decidable (game.accepts s a b) := Classical.decRel _
    (∑ a, ∑ b, if game.accepts s a b then S.prob (game.query s).1 (game.query s).2 a b
      else 0) = 1 := by
  intro game s S
  classical
  let qr := pauliBraidingSameBasisQuestions roles basis p dummy
  have hq : honestMeasurement qr.1.toBraidingQuestion =
      (honestBasisMeasurement basis).map (basisAnswer qr.1.braidingStrings) := by
    cases roles <;> cases basis <;> rfl
  have hr : honestMeasurement qr.2.toBraidingQuestion =
      (honestBasisMeasurement basis).map (basisAnswer qr.2.braidingStrings) := by
    cases roles <;> cases basis <;> rfl
  change (∑ a, ∑ b, if game.accepts s a b then
    S.prob qr.1.toBraidingQuestion qr.2.toBraidingQuestion a b else 0) = 1
  apply sum_ite_prob_honest_sameBasis basis _ _ _ _ hq hr
  intro u
  change qr.1.braidingCheckedBit (qr.1.braidingStrings.1 ⬝ᵥ u, qr.1.braidingStrings.2 ⬝ᵥ u) =
    qr.2.braidingCheckedBit (qr.2.braidingStrings.1 ⬝ᵥ u, qr.2.braidingStrings.2 ⬝ᵥ u)
  rw [qr.1.braidingCheckedBit_braidingStrings (· ⬝ᵥ u),
    qr.2.braidingCheckedBit_braidingStrings (· ⬝ᵥ u)]
  cases roles <;> cases basis <;> rfl

private theorem honest_special_accepts (roles basis : Bool) (p : ↥(oddPairs (Fin n))) (y : Bool) :
    let game := pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)
    let s := PauliBraidingSeed.special roles basis p y
    let S := (pauliBraidingHonestStrategy n).toCommuting
    letI : ∀ a b, Decidable (game.accepts s a b) := Classical.decRel _
    (∑ a, ∑ b, if game.accepts s a b then S.prob (game.query s).1 (game.query s).2 a b
      else 0) = 1 := by
  intro game s S
  classical
  let q : PauliConsistencyQuestion (Fin n) := ⟨p.val.1, p.val.2, basis⟩
  let r : PauliBraidingQuestion n Bool := .anticommutation true y p
  let f := basisAnswer q.braidingStrings
  let g (u : Fin n → Bool) : BraidingAnswer :=
    .inr ((if y then p.val.2 else p.val.1) ⬝ᵥ u)
  have hq : honestMeasurement q.toBraidingQuestion = (honestBasisMeasurement basis).map f := rfl
  have hr : honestMeasurement r = (honestBasisMeasurement y).map g := by
    change ((honestBasisMeasurement y).map
      ((if y then p.val.2 else p.val.1) ⬝ᵥ ·)).map Sum.inr = _
    rw [Measurement.map_map]
    rfl
  have hcheck (u v : Fin n → Bool) (huv : y = basis → u = v) :
      y = basis → q.braidingCheckedBit (q.braidingStrings.1 ⬝ᵥ u, q.braidingStrings.2 ⬝ᵥ u) =
        (if y then p.val.2 else p.val.1) ⬝ᵥ v := by
    intro hy
    rw [← huv hy, hy]
    exact q.braidingCheckedBit_braidingStrings (· ⬝ᵥ u)
  cases roles
  · apply sum_ite_prob_honest_mapped basis y _ _ f g hq hr
    intro u v huv
    refine hcheck u v ?_
    rintro rfl
    exact not_imp_comm.1 (basisStrategy_prob_eq_zero_of_ne _) huv
  · apply sum_ite_prob_honest_mapped y basis _ _ g f hr hq
    intro v u hvu
    refine hcheck u v ?_
    rintro rfl
    exact (not_imp_comm.1 (basisStrategy_prob_eq_zero_of_ne _) hvu).symm

/-- The honest strategy passes the consistency branch with probability one. -/
theorem quantumWinProb_pauliBraidingHonestStrategy_consistency :
    (pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id) 2).quantumWinProb
      (pauliBraidingHonestStrategy n) = 1 := by
  classical
  let := oddPairs_nonempty (ι := Fin n)
  let game := pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)
  let S := (pauliBraidingHonestStrategy n).toCommuting
  let uniform (T : Type) [Fintype T] [Nonempty T] := Probability.PMF.uniformOfFintype T
  let law : Bool × Bool × Bool → PMF (PauliBraidingSeed n Bool) :=
    fun (roles, basis, specialRound) =>
      pauliBraidingConsistencyLaw n TwoProverGame.chsh.questions roles basis specialRound
  rw [← SeededGame.commutingWinProb_toCommuting]
  change ({ game with seed := (uniform (Bool × Bool × Bool)).bind law }).answersWinProb S.answers =
    1
  rw [SeededGame.answersWinProb_bind_uniformSeed]
  refine (expect_congr rfl fun ⟨roles, basis, specialRound⟩ _ => ?_).trans (Fintype.expect_const _)
  cases specialRound
  · let T := ↥(oddPairs (Fin n)) × (Fin n → Bool)
    let f : T → PauliBraidingSeed n Bool := fun (p, dummy) => .sameBasis roles basis p dummy
    let g := game.pullbackSeed (uniform T) f
    change ({ game with seed := (uniform T).map f }).answersWinProb S.answers = 1
    rw [← game.answersWinProb_pullbackSeed]
    change g.commutingWinProb S = 1
    rw [SeededGame.commutingWinProb_eq_expect_of_uniform g rfl]
    exact (expect_congr rfl fun ⟨p, dummy⟩ _ => honest_sameBasis_accepts roles basis p dummy).trans
      (Fintype.expect_const _)
  · let T := ↥(oddPairs (Fin n))
    let f : Bool → T → PauliBraidingSeed n Bool := fun y p => .special roles basis p y
    let marginal := TwoProverGame.chsh.questions.map Prod.snd
    change ({ game with seed := marginal.bind fun y => (uniform T).map (f y) }).answersWinProb
      S.answers = 1
    rw [SeededGame.answersWinProb_bind_seed]
    have hy (y : Bool) : ({ game with seed := (uniform T).map (f y) }).answersWinProb S.answers =
        1 := by
      rw [← game.answersWinProb_pullbackSeed]
      let g := game.pullbackSeed (uniform T) (f y)
      change g.commutingWinProb S = 1
      rw [SeededGame.commutingWinProb_eq_expect_of_uniform g rfl]
      exact (expect_congr rfl fun p _ => honest_special_accepts roles basis p y).trans
        (Fintype.expect_const _)
    simp only [hy, mul_one, Probability.PMF.sum_toReal]

/-- The honest strategy attains the mean of the perfect linearity and consistency scores
and the optimal CHSH score. -/
theorem quantumWinProb_pauliBraidingHonestStrategy :
    (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb
      (pauliBraidingHonestStrategy n) = (2 + Real.cos (π / 8) ^ 2) / 3 := by
  rw [SeededGame.quantumWinProb, answersWinProb_pauliBraidingGame, Fin.sum_univ_three]
  let G := pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id)
  let S := pauliBraidingHonestStrategy n
  change ((G 0).quantumWinProb S + (G 1).quantumWinProb S + (G 2).quantumWinProb S) / 3 = _
  rw [quantumWinProb_pauliBraidingHonestStrategy_linearity,
    quantumWinProb_pauliBraidingHonestStrategy_anticommutation,
    quantumWinProb_pauliBraidingHonestStrategy_consistency]
  ring

/-- The honest score is an upper bound for every finite-dimensional tensor strategy. -/
theorem quantumWinProb_pauliBraidingGame_le {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (S : QuantumStrategy (PauliBraidingQuestion n Bool) (PauliBraidingQuestion n Bool)
      ((Bool × Bool) ⊕ Bool) ((Bool × Bool) ⊕ Bool) I K) :
    (pauliBraidingGame n TwoProverGame.chsh id (fun _ => id)).quantumWinProb S ≤
      (2 + Real.cos (π / 8) ^ 2) / 3 := by
  rw [← SeededGame.commutingWinProb_toCommuting, SeededGame.commutingWinProb,
    answersWinProb_pauliBraidingGame, Fin.sum_univ_three]
  let G := pauliBraidingBranchGame n TwoProverGame.chsh id (fun _ => id)
  have h₀ := (G 0).answersWinProb_le_one S.toCommuting.answers
  have h₁ := commutingWinProb_pauliBraidingAnticommutation_le S.toCommuting
  have h₂ := (G 2).answersWinProb_le_one S.toCommuting.answers
  change (G 1).answersWinProb S.toCommuting.answers ≤ _ at h₁
  change ((G 0).answersWinProb S.toCommuting.answers +
    (G 1).answersWinProb S.toCommuting.answers + (G 2).answersWinProb S.toCommuting.answers) / 3 ≤ _
  linarith only [h₀, h₁, h₂]

end Consistency

end Cslib.PCP
