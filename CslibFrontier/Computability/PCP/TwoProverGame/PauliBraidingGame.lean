/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.ConsistencyTest
public import CslibFrontier.Computability.PCP.TwoProverGame.SymmetricLinearity

/-!
# The Pauli braiding verifier

This is a seeded verifier based on [Natarajan and Vidick, Figure 2][NatarajanVidick2017]
(arXiv:1610.03574v1, p. 17), for any anticommutation game with a common question and answer
alphabet for its two roles. A uniform branch choice selects linearity, anticommutation, or
consistency, and a uniform role bit assigns the two physical players to the logical roles.
In the last two branches the pair of strings is uniform among pairs with odd inner
product. The consistency branch chooses the basis and an independent fair coin. One
outcome asks the second player a question from the anticommutation game's second-question
marginal. Agreement is checked when that question is the special question of the chosen
basis. The other outcome compares two basis answers on the shared checked string.

The same-basis check shares the first string in basis X and the second in basis Z, using
the X–Z coordinate convention of equation (11). The same-basis bullet in
Figure 2 writes the shared first string and uses the symbol `N` for the second basis label.
Here both players receive the sampled basis. This check still draws the first player's
pair from the odd-pair law. The checked string is therefore nonzero. Controlling
the uniform averages in Lemma 17 requires additional work at zero. The uniform fixed-role
game in `AveragedConsistency` uses a different seed law.
Basis questions send strings in lexicographic order and are shared by the linearity and
consistency branches. Anticommutation questions carry the pair in X–Z coordinate order so
that each player can identify which string belongs to which observable. This preserves the
labels of the oriented pair even when the Z string comes first lexicographically.
Anticommutation labels distinguish the two logical roles even when their question tokens
coincide. The special consistency round uses the second logical role's label.

## Main definitions

* `Cslib.PCP.PauliBraidingQuestion`: the common visible question type.
* `Cslib.PCP.PauliBraidingSeed`: the four kinds of private seed.
* `Cslib.PCP.pauliBraidingBranchGame`: the verifier conditioned on one branch.
* `Cslib.PCP.pauliBraidingGame`: the joint verifier with private branch and role choices.

## Main results

* `Cslib.PCP.answersWinProb_pauliBraidingGame`: winning probability splits into branch scores.
* `Cslib.PCP.pauliBraidingBranch_deficit_le`: branch deficits are controlled by the full score.
-/

public section

namespace Cslib.PCP

open BitString

/-- A Pauli braiding question. The basis label is `false` for X and `true` for Z. -/
inductive PauliBraidingQuestion (n : ℕ) (Q : Type*)
  /-- Two strings in lexicographic order, to be measured in the same basis. -/
  | basis (zBasis : Bool) (strings : (Fin n → Bool) × (Fin n → Bool))
  /-- A role-tagged question and the strings in X–Z order. `secondRole` denotes the
  second logical role, regardless of the physical player receiving it. -/
  | anticommutation (secondRole : Bool) (question : Q) (strings : ↥(oddPairs (Fin n)))

/-- The private choices for one round of the braiding verifier. In the last three
constructors `swapRoles` is true when the second physical player plays the first logical role. -/
inductive PauliBraidingSeed (n : ℕ) (Q : Type*)
  /-- The linearity branch in one of the two bases. -/
  | linearity (zBasis : Bool) (round : SymmetricLinearitySeed n)
  /-- The anticommutation branch at an odd pair. -/
  | anticommutation (swapRoles : Bool) (strings : ↥(oddPairs (Fin n))) (first second : Q)
  /-- The consistency branch with a question drawn from the second-question marginal. -/
  | special (swapRoles zBasis : Bool) (strings : ↥(oddPairs (Fin n))) (second : Q)
  /-- The consistency branch with an independent dummy string for the second logical player. -/
  | sameBasis (swapRoles zBasis : Bool) (strings : ↥(oddPairs (Fin n))) (dummy : Fin n → Bool)

variable {n : ℕ} {Q A : Type*}

/-- Send a basis question without exposing the unsorted X–Z coordinate order. -/
@[expose] def PauliConsistencyQuestion.toBraidingQuestion (q : PauliConsistencyQuestion (Fin n)) :
    PauliBraidingQuestion n Q :=
  .basis q.basis (cond (lexSwap q.xString q.zString) Prod.swap id (q.xString, q.zString))

/-- Read the bit associated with the checked string from an answer to the sorted basis question. -/
@[expose] def PauliConsistencyQuestion.braidingCheckedBit (q : PauliConsistencyQuestion (Fin n))
    (answer : Bool × Bool) : Bool :=
  q.checkedBit (cond (lexSwap q.xString q.zString) Prod.swap id answer)

/-- The two basis questions before lexicographic sorting, in physical player order. -/
@[expose] def pauliBraidingSameBasisQuestions (swapRoles basis : Bool)
    (p : ↥(oddPairs (Fin n))) (dummy : Fin n → Bool) :
    PauliConsistencyQuestion (Fin n) × PauliConsistencyQuestion (Fin n) :=
  let q : PauliConsistencyQuestion (Fin n) := ⟨p.val.1, p.val.2, basis⟩
  let r := PauliConsistencyQuestion.ofChecked basis (if basis then q.zString else q.xString) dummy
  cond swapRoles Prod.swap id (q, r)

/-- The conditional seed law of the consistency branch. The basis and role are already
fixed, and `specialRound` selects between the special-question and same-basis checks. -/
@[expose] noncomputable def pauliBraidingConsistencyLaw (n : ℕ) [Nonempty (Fin n)]
    (questions : PMF (Q × Q)) (swapRoles basis specialRound : Bool) :
    PMF (PauliBraidingSeed n Q) :=
  letI := oddPairs_nonempty (ι := Fin n)
  let odd := Probability.PMF.uniformOfFintype ↥(oddPairs (Fin n))
  if specialRound then
    (questions.map Prod.snd).bind fun y => odd.map fun strings =>
      .special swapRoles basis strings y
  else
    (Probability.PMF.uniformOfFintype (↥(oddPairs (Fin n)) × (Fin n → Bool))).map
      fun (strings, dummy) => .sameBasis swapRoles basis strings dummy

/-- A verifier conditioned on the linearity (0), anticommutation (1), or consistency (2)
branch. It uses the same questions and checks as the full game. It takes a game, two
distinguished second-player questions and a
bit decoder for each basis. Basis answers are the left summand and anticommutation game
answers are the right summand. Giving an answer from the wrong summand loses, including
in the special branch when the sampled question would otherwise be accepted automatically. -/
@[expose] noncomputable def pauliBraidingBranchGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (branch : Fin 3) :
    SeededGame (PauliBraidingSeed n Q) (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  let pairQuestion (basis : Bool) (p : ↥(oddPairs (Fin n))) :
      PauliConsistencyQuestion (Fin n) := ⟨p.val.1, p.val.2, basis⟩
  letI := oddPairs_nonempty (ι := Fin n)
  let odd := Probability.PMF.uniformOfFintype ↥(oddPairs (Fin n))
  let uniformBit := Probability.PMF.uniformOfFintype Bool
  let law : PMF (PauliBraidingSeed n Q) :=
    if branch = 0 then
      uniformBit.bind fun basis =>
        (symmetricLinearityGame n).seed.map (.linearity basis)
    else if branch = 1 then
      uniformBit.bind fun roles =>
        odd.bind fun strings => G.questions.map fun (x, y) => .anticommutation roles strings x y
    else
      (Probability.PMF.uniformOfFintype (Bool × Bool × Bool)).bind fun
      | (roles, basis, specialRound) =>
        pauliBraidingConsistencyLaw n G.questions roles basis specialRound
  { seed := law
    query := fun
    | .linearity basis r =>
      let (x, y) := (symmetricLinearityGame n).query r
      (.basis basis x, .basis basis y)
    | .anticommutation roles p x y =>
      cond roles Prod.swap id (.anticommutation false x p, .anticommutation true y p)
    | .special roles basis p y =>
      cond roles Prod.swap id
        ((pairQuestion basis p).toBraidingQuestion, .anticommutation true y p)
    | .sameBasis roles basis p dummy =>
      let (q, r) := pauliBraidingSameBasisQuestions roles basis p dummy
      (q.toBraidingQuestion, r.toBraidingQuestion)
    accepts := fun
    | .linearity _ r, .inl a, .inl b => (symmetricLinearityGame n).accepts r a b
    | .linearity .., _, _ => False
    | .anticommutation roles _ x y, .inr a, .inr b =>
      let (a, b) := cond roles Prod.swap id (a, b)
      G.accepts x y a b
    | .anticommutation .., _, _ => False
    | .special roles basis p y, a, b =>
      match cond roles Prod.swap id (a, b) with
      | (.inl bits, .inr answer) =>
        y = special basis → (pairQuestion basis p).braidingCheckedBit bits = decode basis answer
      | _ => False
    | .sameBasis roles basis p dummy, .inl a, .inl b =>
      let (q, r) := pauliBraidingSameBasisQuestions roles basis p dummy
      q.braidingCheckedBit a = r.braidingCheckedBit b
    | .sameBasis .., _, _ => False }

/-- The Pauli braiding verifier with a private uniform choice among the three branches. -/
@[expose] noncomputable def pauliBraidingGame (n : ℕ) [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool) :
    SeededGame (PauliBraidingSeed n Q) (PauliBraidingQuestion n Q) (PauliBraidingQuestion n Q)
      ((Bool × Bool) ⊕ A) ((Bool × Bool) ⊕ A) :=
  let subgame := pauliBraidingBranchGame n G special decode
  { subgame 0 with
    seed := (Probability.PMF.uniformOfFintype (Fin 3)).bind fun branch => (subgame branch).seed }

/-- The full verifier accepts with the mean of the three conditional winning probabilities.
The same answer kernel is used in all branches. -/
theorem answersWinProb_pauliBraidingGame [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A))) :
    (pauliBraidingGame n G special decode).answersWinProb answer =
      (∑ branch, (pauliBraidingBranchGame n G special decode branch).answersWinProb answer) /
        3 := by
  unfold pauliBraidingGame
  rw [SeededGame.answersWinProb_bind_seed]
  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    Nat.cast_ofNat, ← Finset.mul_sum, div_eq_inv_mul]
  rfl

/-- A strategy within `ε` of the mean of the three branch upper bounds is within `3 * ε` of
each bound. The branch scores must be for the same answer kernel. -/
theorem pauliBraidingBranch_deficit_le [Nonempty (Fin n)]
    (G : TwoProverGame Q Q A A) (special : Bool → Q) (decode : Bool → A → Bool)
    (answer : PauliBraidingQuestion n Q → PauliBraidingQuestion n Q →
      PMF (((Bool × Bool) ⊕ A) × ((Bool × Bool) ⊕ A)))
    (upper : Fin 3 → ℝ)
    (hupper : ∀ branch,
      (pauliBraidingBranchGame n G special decode branch).answersWinProb answer ≤ upper branch)
    {ε : ℝ} (hwin :
      (∑ branch, upper branch) / 3 - ε ≤
        (pauliBraidingGame n G special decode).answersWinProb answer)
    (branch : Fin 3) :
    upper branch - (pauliBraidingBranchGame n G special decode branch).answersWinProb answer ≤
      3 * ε := by
  let score (i : Fin 3) := (pauliBraidingBranchGame n G special decode i).answersWinProb answer
  have h := Finset.single_le_sum (f := fun i => upper i - score i)
    (fun i _ => sub_nonneg.mpr (hupper i)) (Finset.mem_univ branch)
  rw [Finset.sum_sub_distrib] at h
  rw [answersWinProb_pauliBraidingGame] at hwin
  change (∑ i, upper i) / 3 - ε ≤ (∑ i, score i) / 3 at hwin
  change upper branch - score branch ≤ _
  linarith

end Cslib.PCP
