/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
public import CslibFrontier.Foundations.Quantum.Bell
public import CslibFrontier.Foundations.Quantum.Pauli
import CslibFrontier.Probability.PMF.Event

/-!
# The magic square game

The **magic square game** in the row–column form of
[Brassard, Broadbent and Tapp, §5.1–5.3][BrassardBroadbentTapp2005] (arXiv:quant-ph/0407221v3,
PDF pp. 21–23): the referee picks a row `r` and a column `c` of a `3 × 3` grid uniformly. Alice
fills row `r` with three bits of even parity, Bob fills column `c` with three bits of odd parity,
and they win when they agree on the shared cell `(r, c)` (`Cslib.PCP.TwoProverGame.magicSquare`).
The square of two-qubit Pauli observables behind it is due to [Mermin][Mermin1990] and
[Peres][Peres1990], who used it for the contextuality of a single system;
[Aravind, §2–3][Aravind2004] made it a game for two observers who are each asked one of all six
lines.

No classical strategy wins with certainty: a grid whose rows have even parity has an even total,
and one whose columns have odd parity has an odd total, so every deterministic strategy loses on
some question. The classical value is exactly `8/9`
(`Cslib.PCP.TwoProverGame.value_magicSquare`).

Entangled provers win with certainty. An *operator solution* replaces the bits by `±1`
observables: self-adjoint involutions `X_{rc}` that commute along each row and each column, whose
rows multiply to `1` and whose columns multiply to `-1`. If Bob holds observables `Y_{rc}` that
commute with Alice's and agree with them perfectly in the shared state, `X_{rc} ≈ Y_{rc}` with error
`0`, then measuring the rows and columns jointly wins with probability `1`
(`Cslib.PCP.TwoProverGame.MagicSquareSolution.commutingWinProb_strategy`). This holds in every
commuting-operator model. It is an algebraic formulation, for this row–column game, of the
direction "operator solution ⇒ perfect strategy" that
[Cleve and Mittal, §2][CleveMittal2014] (arXiv:1209.2729v1, pp. 2–3) prove for
constraint–variable games with the finite-dimensional maximally entangled transpose strategy. The
two-qubit Pauli square of Mermin and Peres is an operator solution, and two EPR pairs make the
agreement perfect, so the entangled value of the magic square is `1`
(`Cslib.PCP.TwoProverGame.quantumValue_magicSquare`).

## Main definitions

* `Cslib.PCP.TwoProverGame.magicSquare`: the magic square game.
* `Cslib.PCP.TwoProverGame.MagicSquareSolution`: operator solutions.
* `Cslib.PCP.TwoProverGame.pauliSolution`: the Mermin–Peres square of two-qubit Pauli observables.
* `Cslib.PCP.TwoProverGame.magicSquareStrategy`: the perfect strategy on two EPR pairs.

## Main results

* `Cslib.PCP.TwoProverGame.value_magicSquare`: the classical value is `8/9`.
* `Cslib.PCP.TwoProverGame.MagicSquareSolution.commutingWinProb_strategy`: operator solutions
  with perfect agreement win with certainty.
* `Cslib.PCP.TwoProverGame.quantumValue_magicSquare`: the entangled value is `1`.
* `Cslib.PCP.TwoProverGame.value_magicSquare_lt_quantumValue`: entanglement strictly helps.

## References

* [G. Brassard, A. Broadbent and A. Tapp, *Quantum pseudo-telepathy*][BrassardBroadbentTapp2005]
* [N. D. Mermin, *Simple unified form for the major no-hidden-variables theorems*][Mermin1990]
* [A. Peres, *Incompatible results of quantum measurements*][Peres1990]
* [P. K. Aravind, *Quantum mysteries revisited again*][Aravind2004]
* [R. Cleve and R. Mittal, *Characterization of binary constraint system
  games*][CleveMittal2014]
-/

@[expose] public section

namespace Cslib.PCP

namespace TwoProverGame

/-- The parity `a₀ ⊕ a₁ ⊕ a₂` of three bits. -/
def xor₃ : Bool × Bool × Bool → Bool
  | (a₀, a₁, a₂) => (a₀ ^^ a₁) ^^ a₂

/-- The entry `i` of three bits. -/
def entry₃ : Bool × Bool × Bool → Fin 3 → Bool
  | (a₀, a₁, a₂) => ![a₀, a₁, a₂]

/-- The **magic square game**: uniform row `r` and column `c`; Alice answers a row of even parity
and Bob a column of odd parity, and they win when they agree on the cell `(r, c)`. -/
noncomputable def magicSquare :
    TwoProverGame (Fin 3) (Fin 3) (Bool × Bool × Bool) (Bool × Bool × Bool) where
  questions := Cslib.Probability.PMF.uniformOfFintype (Fin 3 × Fin 3)
  accepts r c a b := xor₃ a = false ∧ xor₃ b = true ∧ entry₃ a c = entry₃ b r

instance (r c : Fin 3) (a b : Bool × Bool × Bool) : Decidable (magicSquare.accepts r c a b) :=
  inferInstanceAs (Decidable (xor₃ a = false ∧ xor₃ b = true ∧ entry₃ a c = entry₃ b r))

theorem magicSquare_questions_apply (r c : Fin 3) :
    (magicSquare.questions (r, c)).toReal = 1 / 9 := by
  simp [magicSquare, Cslib.Probability.PMF.uniformOfFintype_apply]

/-- Nine bits cannot have rows of even parity and columns of odd parity. -/
private theorem not_magic_grid : ∀ a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : Bool,
    ((a₀₀ ^^ a₀₁) ^^ a₀₂) = false → ((a₁₀ ^^ a₁₁) ^^ a₁₂) = false →
    ((a₂₀ ^^ a₂₁) ^^ a₂₂) = false → ((a₀₀ ^^ a₁₀) ^^ a₂₀) = true →
    ((a₀₁ ^^ a₁₁) ^^ a₂₁) = true → ((a₀₂ ^^ a₁₂) ^^ a₂₂) = true → False := by
  decide

/-- Every deterministic strategy loses on some question: rows of even parity and columns of odd
parity cannot agree on all nine cells. -/
theorem exists_not_accepts_magicSquare (ha hb : Fin 3 → Bool × Bool × Bool) :
    ∃ r c, ¬ magicSquare.accepts r c (ha r) (hb c) := by
  by_contra h
  simp only [not_exists, not_not] at h
  have h₀₀ := h 0 0
  have h₀₁ := h 0 1
  have h₀₂ := h 0 2
  have h₁₀ := h 1 0
  have h₂₀ := h 2 0
  have h₁₁ := h 1 1
  have h₂₁ := h 2 1
  have h₁₂ := h 1 2
  have h₂₂ := h 2 2
  clear h
  generalize ha 0 = A₀ at *
  generalize ha 1 = A₁ at *
  generalize ha 2 = A₂ at *
  generalize hb 0 = B₀ at *
  generalize hb 1 = B₁ at *
  generalize hb 2 = B₂ at *
  obtain ⟨a₀₀, a₀₁, a₀₂⟩ := A₀
  obtain ⟨a₁₀, a₁₁, a₁₂⟩ := A₁
  obtain ⟨a₂₀, a₂₁, a₂₂⟩ := A₂
  obtain ⟨b₀₀, b₀₁, b₀₂⟩ := B₀
  obtain ⟨b₁₀, b₁₁, b₁₂⟩ := B₁
  obtain ⟨b₂₀, b₂₁, b₂₂⟩ := B₂
  simp only [magicSquare, xor₃, entry₃, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at *
  obtain ⟨r₀, c₀, e₀₀⟩ := h₀₀
  obtain ⟨-, c₁, e₀₁⟩ := h₀₁
  obtain ⟨-, c₂, e₀₂⟩ := h₀₂
  obtain ⟨r₁, -, e₁₀⟩ := h₁₀
  obtain ⟨r₂, -, e₂₀⟩ := h₂₀
  obtain ⟨-, -, e₁₁⟩ := h₁₁
  obtain ⟨-, -, e₂₁⟩ := h₂₁
  obtain ⟨-, -, e₁₂⟩ := h₁₂
  obtain ⟨-, -, e₂₂⟩ := h₂₂
  subst e₀₀ e₀₁ e₀₂ e₁₀ e₂₀ e₁₁ e₂₁ e₁₂ e₂₂
  exact not_magic_grid _ _ _ _ _ _ _ _ _ r₀ r₁ r₂ c₀ c₁ c₂

/-- Every deterministic strategy wins the magic square with probability at most `8/9`. -/
theorem winProb_magicSquare_le (ha hb : Fin 3 → Bool × Bool × Bool) :
    magicSquare.winProb ha hb ≤ 8 / 9 := by
  obtain ⟨r, c, hrc⟩ := exists_not_accepts_magicSquare ha hb
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (r, c)), ite_eq_right (by simpa using hrc),
    zero_add]
  calc _ ≤ ∑ _q ∈ Finset.univ.erase (r, c), (1 / 9 : ℝ) := Finset.sum_le_sum fun q _ => by
          split_ifs
          · rw [show q = (q.1, q.2) from rfl, magicSquare_questions_apply]
          · norm_num
    _ = 8 / 9 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      norm_num

/-- A deterministic strategy that loses only on the cell `(2, 2)`. -/
theorem winProb_magicSquare_eq :
    magicSquare.winProb (fun r => if r = 2 then (true, true, false) else (false, false, false))
      (fun _ => (false, false, true)) = 8 / 9 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [magicSquare, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type,
    Fin.sum_univ_three, xor₃, entry₃]
  norm_num

/-- The classical value of the magic square is at most `8/9`. -/
theorem value_magicSquare_le : magicSquare.value ≤ 8 / 9 :=
  ciSup_le fun ha => ciSup_le fun hb => winProb_magicSquare_le ha hb

/-- The classical value of the magic square is `8/9`. -/
theorem value_magicSquare : magicSquare.value = 8 / 9 :=
  le_antisymm value_magicSquare_le (winProb_magicSquare_eq ▸ magicSquare.winProb_le_value _ _)

end TwoProverGame

/-! ### Operator solutions -/

section Operator

open Quantum TwoProverGame
open BitString (signVal)

private theorem signVal_xor₃ (a : Bool × Bool × Bool) :
    (signVal (xor₃ a) : ℂ) =
      signVal (entry₃ a 0) * signVal (entry₃ a 1) * signVal (entry₃ a 2) := by
  obtain ⟨a₀, a₁, a₂⟩ := a
  simp only [xor₃, entry₃, BitString.signVal_xor]
  push_cast
  simp [mul_assoc]

private theorem signVal_ne {t x : Bool} (h : t ≠ x) : (signVal t : ℂ) ≠ signVal x := by
  intro he
  apply h
  cases t <;> cases x <;> first | rfl | norm_num at he

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

private theorem signProj₃_eq (O₀ O₁ O₂ : 𝒜) (a : Bool × Bool × Bool) :
    signProj₃ O₀ O₁ O₂ a = signProj O₀ (entry₃ a 0) * signProj O₁ (entry₃ a 1) *
      signProj O₂ (entry₃ a 2) := by
  obtain ⟨a₀, a₁, a₂⟩ := a
  rfl

omit [Algebra ℂ 𝒜] in
/-- A product of three pairwise commuting factors ends with any of them. -/
private theorem exists_mul₃_eq_mul_right (P : Fin 3 → 𝒜) (h : ∀ i j, Commute (P i) (P j))
    (i : Fin 3) :
    ∃ M, P 0 * P 1 * P 2 = M * P i := by
  fin_cases i
  · exact ⟨P 1 * P 2, by
      simp only [Fin.zero_eta, Fin.isValue]
      rw [(h 0 1).eq, mul_assoc, (h 0 2).eq, ← mul_assoc]⟩
  · exact ⟨P 0 * P 2, by
      simp only [Fin.mk_one, Fin.isValue]
      rw [mul_assoc, (h 1 2).eq, ← mul_assoc]⟩
  · exact ⟨P 0 * P 1, rfl⟩

omit [Algebra ℂ 𝒜] in
/-- A product of three pairwise commuting factors starts with any of them. -/
private theorem exists_mul₃_eq_mul_left (P : Fin 3 → 𝒜) (h : ∀ i j, Commute (P i) (P j))
    (i : Fin 3) :
    ∃ M, P 0 * P 1 * P 2 = P i * M := by
  fin_cases i
  · exact ⟨P 1 * P 2, mul_assoc _ _ _⟩
  · exact ⟨P 0 * P 2, by
      simp only [Fin.mk_one, Fin.isValue]
      rw [(h 0 1).eq, mul_assoc]⟩
  · exact ⟨P 0 * P 1, by
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [mul_assoc, (h 1 2).eq, ← mul_assoc, (h 0 2).eq, mul_assoc]⟩

/-- The joint projection onto outcomes whose sign differs from the product of three commuting
involutions vanishes: if `O₀O₁O₂ = σ_t`, then `P_{a₀}P_{a₁}P_{a₂} = 0` unless `a₀ ⊕ a₁ ⊕ a₂ = t`. -/
theorem signProj₃_eq_zero {O₀ O₁ O₂ : 𝒜} (h₀ : O₀ * O₀ = 1) (h₁ : O₁ * O₁ = 1)
    (h₂ : O₂ * O₂ = 1) (c₀₁ : Commute O₀ O₁) (c₀₂ : Commute O₀ O₂) (c₁₂ : Commute O₁ O₂)
    {t : Bool} (hprod : O₀ * O₁ * O₂ = (signVal t : ℂ) • 1) {a : Bool × Bool × Bool}
    (ha : xor₃ a ≠ t) : signProj₃ O₀ O₁ O₂ a = 0 := by
  rw [signProj₃_eq]
  set P₀ := signProj O₀ (entry₃ a 0)
  set P₁ := signProj O₁ (entry₃ a 1)
  set P₂ := signProj O₂ (entry₃ a 2)
  have key : O₀ * O₁ * O₂ * (P₀ * P₁ * P₂) = (signVal (xor₃ a) : ℂ) • (P₀ * P₁ * P₂) := by
    have d₂₀ : O₂ * P₀ = P₀ * O₂ := (c₀₂.signProj_left _).eq.symm
    have d₂₁ : O₂ * P₁ = P₁ * O₂ := (c₁₂.signProj_left _).eq.symm
    have d₁₀ : O₁ * P₀ = P₀ * O₁ := (c₀₁.signProj_left _).eq.symm
    calc O₀ * O₁ * O₂ * (P₀ * P₁ * P₂) = O₀ * O₁ * (O₂ * P₀) * P₁ * P₂ := by noncomm_ring
      _ = O₀ * (O₁ * P₀) * (O₂ * P₁) * P₂ := by rw [d₂₀]; noncomm_ring
      _ = (O₀ * P₀) * (O₁ * P₁) * (O₂ * P₂) := by rw [d₁₀, d₂₁]; noncomm_ring
      _ = (signVal (xor₃ a) : ℂ) • (P₀ * P₁ * P₂) := by
        rw [mul_signProj h₀, mul_signProj h₁, mul_signProj h₂, signVal_xor₃, smul_mul_smul_comm,
          smul_mul_smul_comm]
  rw [hprod, smul_mul_assoc, one_mul] at key
  have hne : (signVal t : ℂ) - (signVal (xor₃ a) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (signVal_ne (Ne.symm ha))
  have hz : ((signVal t : ℂ) - (signVal (xor₃ a) : ℂ)) • (P₀ * P₁ * P₂) = 0 := by
    rw [sub_smul, key, sub_self]
  rw [← one_smul ℂ (P₀ * P₁ * P₂), ← inv_mul_cancel₀ hne, mul_smul, hz, smul_zero]

end Operator

namespace TwoProverGame

open Quantum

/-- An **operator solution** of the magic square: `±1` observables commuting along each row and
each column, the rows multiplying to `1` and the columns to `-1`. -/
structure MagicSquareSolution (𝒜 : Type*) [Ring 𝒜] [StarRing 𝒜] where
  /-- The observable in row `r` and column `c`. -/
  op : Fin 3 → Fin 3 → 𝒜
  isSelfAdjoint : ∀ r c, IsSelfAdjoint (op r c)
  mul_self : ∀ r c, op r c * op r c = 1
  commute_row : ∀ r c c', Commute (op r c) (op r c')
  commute_col : ∀ r r' c, Commute (op r c) (op r' c)
  row_mul : ∀ r, op r 0 * op r 1 * op r 2 = 1
  col_mul : ∀ c, op 0 c * op 1 c * op 2 c = -1

namespace MagicSquareSolution

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [StarModule ℂ 𝒜] (X : MagicSquareSolution 𝒜)

/-- The joint measurement of the observables of row `r`. -/
noncomputable def rowMeasurement (r : Fin 3) : Measurement (Bool × Bool × Bool) 𝒜 :=
  Measurement.ofInvolution₃ (X.isSelfAdjoint r 0) (X.isSelfAdjoint r 1) (X.isSelfAdjoint r 2)
    (X.mul_self r 0) (X.mul_self r 1) (X.mul_self r 2) (X.commute_row r 0 1)
    (X.commute_row r 0 2) (X.commute_row r 1 2)

/-- The joint measurement of the observables of column `c`. -/
noncomputable def colMeasurement (c : Fin 3) : Measurement (Bool × Bool × Bool) 𝒜 :=
  Measurement.ofInvolution₃ (X.isSelfAdjoint 0 c) (X.isSelfAdjoint 1 c) (X.isSelfAdjoint 2 c)
    (X.mul_self 0 c) (X.mul_self 1 c) (X.mul_self 2 c) (X.commute_col 0 1 c)
    (X.commute_col 0 2 c) (X.commute_col 1 2 c)

theorem rowMeasurement_effect (r : Fin 3) (a : Bool × Bool × Bool) :
    (X.rowMeasurement r).effect a = signProj₃ (X.op r 0) (X.op r 1) (X.op r 2) a :=
  rfl

theorem colMeasurement_effect (c : Fin 3) (b : Bool × Bool × Bool) :
    (X.colMeasurement c).effect b = signProj₃ (X.op 0 c) (X.op 1 c) (X.op 2 c) b :=
  rfl

/-- A row is measured with even parity: the other outcomes have effect `0`. -/
theorem rowMeasurement_effect_eq_zero {r : Fin 3} {a : Bool × Bool × Bool}
    (ha : xor₃ a ≠ false) : (X.rowMeasurement r).effect a = 0 :=
  signProj₃_eq_zero (X.mul_self r 0) (X.mul_self r 1) (X.mul_self r 2) (X.commute_row r 0 1)
    (X.commute_row r 0 2) (X.commute_row r 1 2)
    (by rw [X.row_mul, BitString.signVal_false, Complex.ofReal_one, one_smul]) ha

/-- A column is measured with odd parity: the other outcomes have effect `0`. -/
theorem colMeasurement_effect_eq_zero {c : Fin 3} {b : Bool × Bool × Bool}
    (hb : xor₃ b ≠ true) : (X.colMeasurement c).effect b = 0 :=
  signProj₃_eq_zero (X.mul_self 0 c) (X.mul_self 1 c) (X.mul_self 2 c) (X.commute_col 0 1 c)
    (X.commute_col 0 2 c) (X.commute_col 1 2 c)
    (by rw [X.col_mul, BitString.signVal_true, Complex.ofReal_neg, Complex.ofReal_one,
      neg_one_smul]) hb

omit [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] in
private theorem commute_mul₃ {P Q : Fin 3 → 𝒜} (h : ∀ i j, Commute (P i) (Q j)) :
    Commute (P 0 * P 1 * P 2) (Q 0 * Q 1 * Q 2) := by
  have hl : ∀ j, Commute (P 0 * P 1 * P 2) (Q j) := fun j =>
    ((h 0 j).mul_left (h 1 j)).mul_left (h 2 j)
  exact ((hl 0).mul_right (hl 1)).mul_right (hl 2)

/-- The commuting-operator strategy of two operator solutions: Alice measures the rows of `X`,
Bob the columns of `Y`, in the state `φ`; Alice's observables commute with Bob's. -/
noncomputable def strategy (Y : MagicSquareSolution 𝒜) (φ : AlgState 𝒜)
    (hXY : ∀ r c r' c', Commute (X.op r c) (Y.op r' c')) :
    CommutingStrategy (Fin 3) (Fin 3) (Bool × Bool × Bool) (Bool × Bool × Bool) 𝒜 where
  state := φ
  alice := X.rowMeasurement
  bob := Y.colMeasurement
  commute r c a b := by
    rw [rowMeasurement_effect, colMeasurement_effect, signProj₃_eq, signProj₃_eq]
    exact commute_mul₃ (P := fun i => signProj (X.op r i) (entry₃ a i))
      (Q := fun j => signProj (Y.op j c) (entry₃ b j)) fun i j => (hXY r i j c).signProj _ _

variable [SelfAdjointDecompose 𝒜]

/-- **Transfer of a column**: if Bob's observables `Y_i` agree perfectly in the state with Alice's
`X_i` and commute with them, Bob's joint projection can be replaced by Alice's, in reverse order. -/
theorem apply_mul_signProj₃_eq (φ : AlgState 𝒜) {Xc Yc : Fin 3 → 𝒜}
    (h : ∀ i, Xc i ≈[φ; 0] Yc i) (hc : ∀ i j, Commute (Yc i) (Xc j)) (E : 𝒜)
    (b : Bool × Bool × Bool) :
    φ (E * signProj₃ (Yc 0) (Yc 1) (Yc 2) b) = φ (E * (signProj (Xc 2) (entry₃ b 2) *
      signProj (Xc 1) (entry₃ b 1) * signProj (Xc 0) (entry₃ b 0))) := by
  rw [signProj₃_eq]
  set Q : Fin 3 → 𝒜 := fun i => signProj (Yc i) (entry₃ b i) with hQ
  set R : Fin 3 → 𝒜 := fun i => signProj (Xc i) (entry₃ b i) with hR
  have t : ∀ C i, φ (C * Q i) = φ (C * R i) := fun C i =>
    AlgState.apply_mul_signProj_eq_of_approx_zero (h i).symm C _
  have d : ∀ i j, Commute (Q i) (R j) := fun i j => (hc i j).signProj _ _
  change φ (E * (Q 0 * Q 1 * Q 2)) = φ (E * (R 2 * R 1 * R 0))
  calc φ (E * (Q 0 * Q 1 * Q 2)) = φ ((E * Q 0 * Q 1) * Q 2) := by simp only [mul_assoc]
    _ = φ ((E * Q 0 * Q 1) * R 2) := t _ 2
    _ = φ ((E * Q 0 * R 2) * Q 1) := by rw [mul_assoc (E * Q 0), (d 1 2).eq, ← mul_assoc]
    _ = φ ((E * Q 0 * R 2) * R 1) := t _ 1
    _ = φ ((E * R 2 * R 1) * Q 0) := by
      rw [mul_assoc E, (d 0 2).eq, ← mul_assoc, mul_assoc (E * R 2), (d 0 1).eq, ← mul_assoc]
    _ = φ ((E * R 2 * R 1) * R 0) := t _ 0
    _ = φ (E * (R 2 * R 1 * R 0)) := by simp only [mul_assoc]

/-- In the strategy of two perfectly agreeing operator solutions, the answers are rejected with
probability `0`. -/
theorem apply_effect_mul_effect_eq_zero (Y : MagicSquareSolution 𝒜) (φ : AlgState 𝒜)
    (hXY : ∀ r c r' c', Commute (X.op r c) (Y.op r' c'))
    (hagree : ∀ r c, X.op r c ≈[φ; 0] Y.op r c) {r c : Fin 3} {a b : Bool × Bool × Bool}
    (hrej : ¬ magicSquare.accepts r c a b) :
    φ ((X.rowMeasurement r).effect a * (Y.colMeasurement c).effect b) = 0 := by
  simp only [magicSquare, not_and] at hrej
  by_cases ha : xor₃ a = false
  swap
  · rw [X.rowMeasurement_effect_eq_zero ha, zero_mul, map_zero]
  by_cases hb : xor₃ b = true
  swap
  · rw [Y.colMeasurement_effect_eq_zero hb, mul_zero, map_zero]
  have he := hrej ha hb
  rw [colMeasurement_effect, apply_mul_signProj₃_eq φ (Xc := fun i => X.op i c)
    (Yc := fun i => Y.op i c) (fun i => hagree i c) (fun i j => (hXY j c i c).symm)]
  set R : Fin 3 → 𝒜 := fun i => signProj (X.op i c) (entry₃ b i)
  set P : Fin 3 → 𝒜 := fun i => signProj (X.op r i) (entry₃ a i)
  have hRc : ∀ i j, Commute (R i) (R j) := fun i j => (X.commute_col i j c).signProj _ _
  have hPc : ∀ i j, Commute (P i) (P j) := fun i j => (X.commute_row r i j).signProj _ _
  have hrev : R 2 * R 1 * R 0 = R 0 * R 1 * R 2 := by
    rw [(hRc 2 1).eq, mul_assoc, (hRc 2 0).eq, ← mul_assoc, (hRc 1 0).eq]
  obtain ⟨M, hM⟩ := exists_mul₃_eq_mul_right P hPc c
  obtain ⟨M', hM'⟩ := exists_mul₃_eq_mul_left R hRc r
  have hE : (X.rowMeasurement r).effect a = M * P c := by
    rw [rowMeasurement_effect, signProj₃_eq]; exact hM
  have hzero : P c * R r = 0 :=
    signProj_mul_signProj_of_ne (X.mul_self r c) he
  change φ ((X.rowMeasurement r).effect a * (R 2 * R 1 * R 0)) = 0
  rw [hrev, hE, hM', show M * P c * (R r * M') = M * (P c * R r) * M' by noncomm_ring, hzero,
    mul_zero, zero_mul, map_zero]

variable [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

/-- **Operator solutions win the magic square with certainty**: if Alice measures the rows of an
operator solution `X` and Bob the columns of an operator solution `Y`, with Alice's observables
commuting with Bob's and agreeing with them perfectly in the shared state, they win with
probability `1`. This generalizes the transpose strategy of [Cleve and Mittal, §2][CleveMittal2014]
from finite dimensions to any commuting-operator model. -/
theorem commutingWinProb_strategy (Y : MagicSquareSolution 𝒜) (φ : AlgState 𝒜)
    (hXY : ∀ r c r' c', Commute (X.op r c) (Y.op r' c'))
    (hagree : ∀ r c, X.op r c ≈[φ; 0] Y.op r c) :
    magicSquare.commutingWinProb (X.strategy Y φ hXY) = 1 := by
  set S := X.strategy Y φ hXY
  have hsum : ∀ r c, (∑ a, ∑ b, if magicSquare.accepts r c a b then S.prob r c a b else 0) = 1 :=
    fun r c => by
      rw [← S.sum_prob r c]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rfl
      · have := X.apply_effect_mul_effect_eq_zero Y φ hXY hagree h
        simp only [CommutingStrategy.prob]
        change 0 = (φ ((X.rowMeasurement r).effect a * (Y.colMeasurement c).effect b)).re
        rw [this, Complex.zero_re]
  rw [commutingWinProb_eq_sum]
  simp only [hsum, magicSquare_questions_apply, mul_one, Fin.sum_univ_three]
  norm_num

end MagicSquareSolution

end TwoProverGame

/-! ### The Pauli square -/

namespace TwoProverGame

namespace MagicSquareSolution

open Quantum Matrix

private theorem mul₃_comm_rev {𝒜 : Type*} [Ring 𝒜] {a b c : 𝒜} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) : a * b * c = c * b * a := by
  rw [hab.eq, mul_assoc, hac.eq, ← mul_assoc, hbc.eq]

/-- The image of an operator solution under a star-algebra homomorphism. -/
noncomputable def map {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B]
    [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (X : MagicSquareSolution A) : MagicSquareSolution B where
  op r c := f (X.op r c)
  isSelfAdjoint r c := (X.isSelfAdjoint r c).map f
  mul_self r c := by rw [← map_mul, X.mul_self, map_one]
  commute_row r c c' := (X.commute_row r c c').map f
  commute_col r r' c := (X.commute_col r r' c).map f
  row_mul r := by rw [← map_mul, ← map_mul, X.row_mul, map_one]
  col_mul c := by rw [← map_mul, ← map_mul, X.col_mul, map_neg, map_one]

/-- The transpose of an operator solution in a matrix algebra. -/
def transpose {n : Type*} [Fintype n] [DecidableEq n] (X : MagicSquareSolution (Matrix n n ℂ)) :
    MagicSquareSolution (Matrix n n ℂ) where
  op r c := (X.op r c)ᵀ
  isSelfAdjoint r c := by
    change (X.op r c)ᵀᴴ = (X.op r c)ᵀ
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
    exact congrArg Matrix.transpose (X.isSelfAdjoint r c)
  mul_self r c := by rw [← Matrix.transpose_mul, X.mul_self, Matrix.transpose_one]
  commute_row r c c' := by
    change _ * _ = _ * _
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, (X.commute_row r c c').eq]
  commute_col r r' c := by
    change _ * _ = _ * _
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, (X.commute_col r r' c).eq]
  row_mul r := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← mul_assoc,
      ← mul₃_comm_rev (X.commute_row r 0 1) (X.commute_row r 0 2) (X.commute_row r 1 2),
      X.row_mul, Matrix.transpose_one]
  col_mul c := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← mul_assoc,
      ← mul₃_comm_rev (X.commute_col 0 1 c) (X.commute_col 0 2 c) (X.commute_col 1 2 c),
      X.col_mul, Matrix.transpose_neg, Matrix.transpose_one]

end MagicSquareSolution

open Matrix Quantum
open scoped Kronecker MatrixOrder ComplexOrder

private theorem neg_kronecker' {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [kroneckerMap_apply]

private theorem kronecker_neg' {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [kroneckerMap_apply]

private theorem pauliX_mul_pauliX_mul (M : Matrix Bool Bool ℂ) : pauliX * (pauliX * M) = M := by
  rw [← Matrix.mul_assoc, pauliX_mul_self, Matrix.one_mul]

private theorem pauliZ_mul_pauliZ_mul (M : Matrix Bool Bool ℂ) : pauliZ * (pauliZ * M) = M := by
  rw [← Matrix.mul_assoc, pauliZ_mul_self, Matrix.one_mul]

private theorem pauliZ_mul_pauliX_mul (M : Matrix Bool Bool ℂ) :
    pauliZ * (pauliX * M) = -(pauliX * (pauliZ * M)) := by
  rw [← Matrix.mul_assoc, pauliZ_mul_pauliX, Matrix.neg_mul, Matrix.mul_assoc]

/-- The **Mermin–Peres square** of two-qubit Pauli observables: its rows multiply to `1` and its
columns to `-1`. -/
noncomputable def pauliSquare : Fin 3 → Fin 3 → Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  ![![pauliX ⊗ₖ 1, 1 ⊗ₖ pauliX, pauliX ⊗ₖ pauliX],
    ![1 ⊗ₖ pauliZ, pauliZ ⊗ₖ 1, pauliZ ⊗ₖ pauliZ],
    ![(-pauliX) ⊗ₖ pauliZ, (-pauliZ) ⊗ₖ pauliX, (pauliZ * pauliX) ⊗ₖ (pauliX * pauliZ)]]

attribute [local simp] pauliX_mul_self pauliZ_mul_self pauliZ_mul_pauliX pauliX_mul_pauliX_mul
  pauliZ_mul_pauliZ_mul pauliZ_mul_pauliX_mul Matrix.mul_assoc Matrix.neg_mul Matrix.mul_neg
  neg_neg Matrix.one_mul Matrix.mul_one one_kronecker_one neg_kronecker' kronecker_neg' pauliSquare
  conjTranspose_kronecker conjTranspose_one conjTranspose_neg conjTranspose_mul

/-- The Mermin–Peres square is an operator solution of the magic square. -/
noncomputable def pauliSolution : MagicSquareSolution (Matrix (Bool × Bool) (Bool × Bool) ℂ) where
  op := pauliSquare
  isSelfAdjoint r c := by
    have hX := pauliX_isHermitian.eq
    have hZ := pauliZ_isHermitian.eq
    change (pauliSquare r c)ᴴ = pauliSquare r c
    fin_cases r <;> fin_cases c <;> simp [hX, hZ]
  mul_self r c := by fin_cases r <;> fin_cases c <;> simp [← mul_kronecker_mul]
  commute_row r c c' := by
    fin_cases r <;> fin_cases c <;> fin_cases c' <;>
      simp [Commute, SemiconjBy, ← mul_kronecker_mul]
  commute_col r r' c := by
    fin_cases r <;> fin_cases r' <;> fin_cases c <;>
      simp [Commute, SemiconjBy, ← mul_kronecker_mul]
  row_mul r := by fin_cases r <;> simp [← mul_kronecker_mul]
  col_mul c := by fin_cases c <;> simp [← mul_kronecker_mul]

/-- The **perfect strategy** for the magic square: Alice and Bob share two EPR pairs, Alice
measures the rows of the Mermin–Peres square and Bob the columns of its transpose. -/
noncomputable def magicSquareStrategy :
    QuantumStrategy (Fin 3) (Fin 3) (Bool × Bool × Bool) (Bool × Bool × Bool) (Bool × Bool)
      (Bool × Bool) where
  state := maxEntangled (Bool × Bool)
  norm_state := norm_maxEntangled
  alice r := (pauliSolution.rowMeasurement r).toPOVM
  bob c := (pauliSolution.transpose.colMeasurement c).toPOVM

private theorem commutingStrategy_ext {X Y A B 𝒜 : Type*} [Fintype A] [Fintype B] [Ring 𝒜]
    [PartialOrder 𝒜] [Algebra ℂ 𝒜] {S T : CommutingStrategy X Y A B 𝒜}
    (hs : S.state = T.state) (ha : ∀ x, S.alice x = T.alice x) (hb : ∀ y, S.bob y = T.bob y) :
    S = T := by
  obtain ⟨φ, P, Q, h⟩ := S
  obtain ⟨φ', P', Q', h'⟩ := T
  simp only at hs ha hb
  subst hs
  obtain rfl : P = P' := funext ha
  obtain rfl : Q = Q' := funext hb
  rfl

/-- The perfect strategy is the strategy of the Mermin–Peres square, embedded in Alice's and Bob's
halves, and its transpose. -/
theorem toCommuting_magicSquareStrategy :
    magicSquareStrategy.toCommuting = (pauliSolution.map kroneckerOne).strategy
      (pauliSolution.transpose.map oneKronecker)
      (AlgState.vector (maxEntangled (Bool × Bool)) norm_maxEntangled)
      (fun _ _ _ _ => commute_kroneckerOne_oneKronecker _ _) := by
  refine commutingStrategy_ext rfl (fun r => Measurement.ext fun a => ?_)
    (fun c => Measurement.ext fun b => ?_)
  · change (signProj₃ _ _ _ a) ⊗ₖ 1 = signProj₃ _ _ _ a
    rw [← kroneckerOne_apply, signProj₃_eq, signProj₃_eq, map_mul, map_mul, map_signProj,
      map_signProj, map_signProj]
    rfl
  · change 1 ⊗ₖ (signProj₃ _ _ _ b) = signProj₃ _ _ _ b
    rw [← oneKronecker_apply, signProj₃_eq, signProj₃_eq, map_mul, map_mul, map_signProj,
      map_signProj, map_signProj]
    rfl

/-- The perfect strategy wins the magic square with certainty. -/
theorem quantumWinProb_magicSquareStrategy :
    magicSquare.quantumWinProb magicSquareStrategy = 1 := by
  rw [← commutingWinProb_toCommuting, toCommuting_magicSquareStrategy]
  refine MagicSquareSolution.commutingWinProb_strategy _ _ _ _ fun r c => ?_
  exact AlgState.kroneckerOne_approx_oneKronecker_transpose (pauliSolution.isSelfAdjoint r c)
    (pauliSolution.mul_self r c)

/-- **The entangled value of the magic square is `1`**: two EPR pairs win with certainty. -/
theorem quantumValue_magicSquare : magicSquare.quantumValue = 1 :=
  le_antisymm (quantumValue_le_one _)
    (quantumWinProb_magicSquareStrategy ▸ quantumWinProb_le_quantumValue _ _)

/-- **Quantum pseudo-telepathy**: entanglement wins the magic square with certainty, while every
classical strategy loses with probability at least `1/9`. -/
theorem value_magicSquare_lt_quantumValue : magicSquare.value < magicSquare.quantumValue := by
  rw [quantumValue_magicSquare]
  linarith [value_magicSquare_le]

end TwoProverGame

end Cslib.PCP
