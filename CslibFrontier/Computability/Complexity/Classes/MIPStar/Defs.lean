/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Quantum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Cslib.Probability.PMF

/-!
# Entangled two-prover one-round proofs: the class `MIP*`

A *game verifier* (`Cslib.Complexity.GameVerifier`) on instances `α` plays one round with two
provers. On an instance `a` it draws a uniformly random seed of `p(|enc a|)` bits, computes from
`a` and the seed a pair of questions `(x, y)`, sends `x` to the first prover and `y` to the second,
receives answers of `p(|enc a|)` bits each and accepts by a decision predicate on `a`, the
questions and the answers. The game it plays on `a` is the two-prover one-round game
`Cslib.Complexity.GameVerifier.game` of `Cslib.PCP.TwoProverGame`.

The provers of `MIP*` share an entangled state: their strategies are the finite-dimensional
tensor-product strategies `Cslib.PCP.TwoProverGame.QuantumStrategy`, and the success probability
of the best provers is the entangled value `Cslib.PCP.TwoProverGame.quantumValue`, a supremum over
all finite dimensions. A problem is in `MIP* = MIP*_{1,1/2}(2,1)` (`Cslib.Complexity.MIPStar`) when
a verifier whose sampler and decider run in polynomial time plays a game of entangled value `1`
on every instance in the problem and at most `1/2` on every other instance
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020].

This is the model in which `MIP* = RE` holds. The classical class `Cslib.Complexity.MIP` lets the
provers interact over several rounds but gives them no shared entanglement, and the
commuting-operator model, in which the provers' measurements commute on one Hilbert space, is not
formalized.

## Main definitions

* `Cslib.Complexity.GameVerifier`: a sampler, a decider and the polynomial length of seeds and
  answers.
* `Cslib.Complexity.GameVerifier.game`: the game the verifier plays on an instance.
* `Cslib.Complexity.GameVerifier.IsPolyTime`: the sampler and the decider run in polynomial time.
* `Cslib.Complexity.MIPStar`: the class `MIP*_{1,1/2}(2,1)`.

## Main results

* `Cslib.Complexity.GameVerifier.quantumValue_game_eq_one_of_forall`: a verifier that accepts all
  answers plays a game of entangled value `1`.
* `Cslib.Complexity.GameVerifier.quantumValue_game_eq_zero_of_forall`: a verifier that rejects all
  answers plays a game of entangled value `0`.
* `Cslib.Complexity.empty_mem_MIPStar`, `Cslib.Complexity.univ_mem_MIPStar`: the trivial problems
  are in `MIP*`.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.PCP Cslib.Probability Turing.MultiTapeTM

variable {α : Type}

/-- A two-prover one-round verifier on instances `α`: on the instance `a`, seeds and answers have
`length.eval |enc a|` bits, `sample (a, r)` computes the questions from the seed `r`, and
`decide (a, (x, y), (u, v))` accepts the answers `u` and `v` to the questions `x` and `y`
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020]. -/
structure GameVerifier (α : Type) where
  /-- The length of the seed and of each answer, as a polynomial in the instance length. -/
  length : Polynomial ℕ
  /-- The question pair computed from the instance and the seed. -/
  sample : α × List Bool → List Bool × List Bool
  /-- The decision on the instance, the questions and the answers. -/
  decide : α × (List Bool × List Bool) × (List Bool × List Bool) → Bool

namespace GameVerifier

variable (V : GameVerifier α) (enc : α ↪ List Bool)

/-- The length of seeds and answers on the instance `a`. -/
abbrev bound (a : α) : ℕ := V.length.eval (enc a).length

/-- The game played on the instance `a`: the questions are sampled from a uniform seed of
`V.bound enc a` bits, the answers are words of that length, and the decider accepts. -/
noncomputable def game (a : α) :
    TwoProverGame (List Bool) (List Bool) (Fin (V.bound enc a) → Bool)
      (Fin (V.bound enc a) → Bool) where
  questions := (PMF.uniformOfFintype (Fin (V.bound enc a) → Bool)).map fun r =>
    V.sample (a, List.ofFn r)
  accepts x y u v := V.decide (a, (x, y), (List.ofFn u, List.ofFn v)) = true

/-- The sampler and the decider run in polynomial time, on the instance encoded by `enc`. -/
structure IsPolyTime : Prop where
  sample : ComputableInPolyTime V.sample (encPair enc encBits) (encPair encBits encBits)
  decide : ComputableInPolyTime V.decide
    (encPair enc (encPair (encPair encBits encBits) (encPair encBits encBits))) encBool

/-- A verifier that accepts all answers plays a game of entangled value `1`. -/
theorem quantumValue_game_eq_one_of_forall {a : α} (h : ∀ q w, V.decide (a, q, w) = true) :
    (V.game enc a).quantumValue = 1 := by
  classical
  refine le_antisymm (TwoProverGame.quantumValue_le_one _) ?_
  have hwin := (V.game enc a).quantumWinProb_le_quantumValue
    (QuantumStrategy.ofDeterministic (X := List Bool) (Y := List Bool)
      (A := Fin (V.bound enc a) → Bool) (B := Fin (V.bound enc a) → Bool)
      (fun _ _ => false) (fun _ _ => false))
  rw [TwoProverGame.quantumWinProb_ofDeterministic] at hwin
  refine le_trans (le_of_eq ?_) hwin
  simp [TwoProverGame.winProb, game, h]

/-- A verifier that rejects all answers plays a game of entangled value `0`. -/
theorem quantumValue_game_eq_zero_of_forall {a : α} (h : ∀ q w, V.decide (a, q, w) = false) :
    (V.game enc a).quantumValue = 0 := by
  refine le_antisymm ((V.game enc a).quantumValue_le le_rfl fun S => ?_)
    (TwoProverGame.quantumValue_nonneg _)
  simp [TwoProverGame.quantumWinProb, game, h]

end GameVerifier

/-- **The class `MIP* = MIP*_{1,1/2}(2,1)`**: the problems with a polynomial-time two-prover
one-round verifier whose game has entangled value `1` on the instances in the problem and at most
`1/2` on the others, with respect to the encoding `enc` of instances
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020]. -/
def MIPStar (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ V : GameVerifier α, V.IsPolyTime enc ∧ ∀ a,
    (a ∈ A → (V.game enc a).quantumValue = 1) ∧ (a ∉ A → (V.game enc a).quantumValue ≤ 1 / 2)}

theorem mem_MIPStar {enc : α ↪ List Bool} {A : Set α} :
    A ∈ MIPStar enc ↔ ∃ V : GameVerifier α, V.IsPolyTime enc ∧ ∀ a,
      (a ∈ A → (V.game enc a).quantumValue = 1) ∧
        (a ∉ A → (V.game enc a).quantumValue ≤ 1 / 2) :=
  Iff.rfl

/-- The verifier with constant questions and the constant decision `b`. -/
noncomputable def GameVerifier.const (b : Bool) : GameVerifier α where
  length := 0
  sample _ := ([], [])
  decide _ := b

theorem GameVerifier.isPolyTime_const (enc : α ↪ List Bool) (b : Bool) :
    (GameVerifier.const (α := α) b).IsPolyTime enc :=
  ⟨ComputableInPolyTime.const _, ComputableInPolyTime.const _⟩

/-- The empty problem is in `MIP*`. -/
theorem empty_mem_MIPStar (enc : α ↪ List Bool) : (∅ : Set α) ∈ MIPStar enc :=
  ⟨.const false, GameVerifier.isPolyTime_const enc false, fun a =>
    ⟨fun h => h.elim, fun _ => by
      rw [GameVerifier.quantumValue_game_eq_zero_of_forall _ _ fun _ _ => rfl]
      norm_num⟩⟩

/-- The problem of all instances is in `MIP*`. -/
theorem univ_mem_MIPStar (enc : α ↪ List Bool) : (Set.univ : Set α) ∈ MIPStar enc :=
  ⟨.const true, GameVerifier.isPolyTime_const enc true, fun _ =>
    ⟨fun _ => GameVerifier.quantumValue_game_eq_one_of_forall _ _ fun _ _ => rfl,
      fun h => (h trivial).elim⟩⟩

end Cslib.Complexity
