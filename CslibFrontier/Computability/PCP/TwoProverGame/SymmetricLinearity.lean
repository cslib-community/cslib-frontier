/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Linearity
public import CslibFrontier.Foundations.Data.BitString.Lex

/-!
# The symmetric linearity game

In Figure 1 of [Natarajan and Vidick][NatarajanVidick2017] (arXiv:1610.03574v1),
both players answer a pair of strings in lexicographic order. The verifier assigns roles
uniformly at random. The pair player receives two independent uniform strings; the point
player receives the selected linearity query together with an independent uniform dummy.
The verifier tracks which coordinate carries each answer when sorting the questions.

## Main results

* `Cslib.PCP.symmetricLinearityGame_accepts_linear`: honest linear answers pass every seed.

## Main definitions

* `Cslib.PCP.SymmetricLinearitySeed`: the verifier's private choices.
* `Cslib.PCP.symmetricLinearityGame`: the seeded game with random roles and sorted questions.
-/

public section

namespace Cslib.PCP

/-- Private choices for a round of the symmetric linearity game. -/
structure SymmetricLinearitySeed (n : ℕ) where
  /-- Whether the second player receives the original pair. -/
  swapRoles : Bool
  /-- Which point query and acceptance check the verifier uses. -/
  check : Fin 3
  /-- The first string of the original pair before sorting. -/
  first : Fin n → Bool
  /-- The second string of the original pair before sorting. -/
  second : Fin n → Bool
  /-- The point player's independent dummy string. -/
  dummy : Fin n → Bool

instance {n : ℕ} : Fintype (SymmetricLinearitySeed n) :=
  Fintype.ofEquiv (Bool × Fin 3 × (Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool))
    { toFun := fun (roles, k, a, b, dummy) => ⟨roles, k, a, b, dummy⟩
      invFun := fun seed => (seed.swapRoles, seed.check, seed.first, seed.second, seed.dummy)
      left_inv := by rintro ⟨_, _, _, _, _⟩; rfl
      right_inv := fun _ => rfl }

instance {n : ℕ} : Nonempty (SymmetricLinearitySeed n) :=
  ⟨⟨false, 0, 0, 0, 0⟩⟩

/-- The symmetric two-player linearity game. The seed specifies the role assignment, the
check, the pair player's two strings and the point player's dummy. The check remains indexed
by the sampled choice even when candidate query strings coincide. -/
@[expose] noncomputable def symmetricLinearityGame (n : ℕ) :
    SeededGame (SymmetricLinearitySeed n)
      ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool))
      (Bool × Bool) (Bool × Bool) :=
  { seed := Probability.PMF.uniformOfFintype _
    query := fun
    | ⟨swapRoles, k, a, b, dummy⟩ =>
      let c := linearityQuery k a b
      let pair := cond (BitString.lexSwap a b) Prod.swap id (a, b)
      let point := cond (BitString.lexSwap c dummy) Prod.swap id (c, dummy)
      cond swapRoles Prod.swap id (pair, point)
    accepts := fun
    | ⟨swapRoles, k, a, b, dummy⟩, alice, bob =>
      let (pair, point) := cond swapRoles Prod.swap id (alice, bob)
      let c := linearityQuery k a b
      (cond (BitString.lexSwap c dummy) Prod.swap id point).1 =
        linearityCheck k (cond (BitString.lexSwap a b) Prod.swap id pair) }

instance {n : ℕ} (seed : SymmetricLinearitySeed n)
    (alice bob : Bool × Bool) : Decidable ((symmetricLinearityGame n).accepts seed alice bob) := by
  rcases seed with ⟨swapRoles, k, a, b, dummy⟩
  unfold symmetricLinearityGame
  dsimp only
  infer_instance

/-- Evaluating one additive Boolean function at both visible coordinates always passes,
for every width and private seed. -/
theorem symmetricLinearityGame_accepts_linear {n : ℕ} (seed : SymmetricLinearitySeed n)
    (f : (Fin n → Bool) →+ Bool) :
    let game := symmetricLinearityGame n
    let answer (q : (Fin n → Bool) × (Fin n → Bool)) := (f q.1, f q.2)
    game.accepts seed (answer (game.query seed).1) (answer (game.query seed).2) := by
  obtain ⟨roles, k, a, b, dummy⟩ := seed
  have hcheck : f (linearityQuery k a b) = linearityCheck k (f a, f b) := by
    fin_cases k <;> simp [linearityQuery, linearityCheck, map_add, ← Bool.add_eq_xor]
  simp only [symmetricLinearityGame]
  generalize BitString.lexSwap a b = swapPair
  generalize BitString.lexSwap (linearityQuery k a b) dummy = swapPoint
  cases roles <;> cases swapPair <;> cases swapPoint <;> exact hcheck

end Cslib.PCP
