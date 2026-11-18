/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.Nisan
public import CslibFrontier.Probability.SmallBias.Degree
import CslibFrontier.Crypto.Primitives.PRG.Deterministic
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.StatisticalDistance.Event

/-!
# Space-bounded pseudorandom generators are small-bias generators

The parity of the bits of a word in a set `S` of positions is computed by a read-once branching
program with two states (`Cslib.Crypto.PRG.isReadOnceTest_parityOn`). A generator that fools the
read-once programs of width `2 ^ s`, `s ≥ 1`, with error `ε` (an `(s, ε)`-pseudorandom generator
in the sense of [Goldreich, Definition 8.20][Goldreich2007DraftR4]) is therefore a `2ε`-bias
generator (`Cslib.Crypto.PRG.Generator.Secure.isSmallBias`): the bias at `S` is
`2 |Pr[⊕_S G(U) = 1] - 1/2|` (Goldreich's Eq. (8.18)), twice the advantage of the parity test.
With the limitation on small-bias generators of Exercise 8.37
(`Cslib.BitString.card_lt_card_of_isSmallBias`), an `(s, ε)`-pseudorandom generator with
`s ≥ 1` and `ε < 1/2` has stretch `ℓ(k) < 2^k` (`Cslib.Crypto.PRG.Generator.Secure.lt_two_pow`).

**Source qualification.** [Goldreich, Exercise 8.38][Goldreich2007DraftR4] states that an
`(s, ε)`-pseudorandom generator with `s ≥ 1` is an `ε`-bias generator, and Exercise 8.25(2) that
it has `ℓ(k) < 2^k` whenever `ε(k) < 1`, by combining Exercises 8.37 and 8.38. Both printed
claims are false under the source's own definitions: the generator `σ ↦ σσ` on one seed bit is
`(s, 1/2)`-pseudorandom for every `s` (its output is at statistical distance `1/2` from uniform,
so no test whatsoever has advantage above `1/2`), yet its two output bits always have even
parity, bias `1 > 1/2`, and its stretch is `2 = 2^1`
(`Cslib.Crypto.PRG.exists_secure_not_isSmallBias`). The factor `2` above is necessary, and the
corrected endpoints are `2ε`-bias for Exercise 8.38 and `ε < 1/2` for Exercise 8.25(2).

## Main results

* `Cslib.Crypto.PRG.isReadOnceTest_parityOn`: parities are read-once tests of width `2`.
* `Cslib.Crypto.PRG.Generator.Secure.isSmallBias`: Exercise 8.38, corrected to `2ε`.
* `Cslib.Crypto.PRG.Generator.Secure.lt_two_pow`: Exercise 8.25(2), corrected to `ε < 1/2`.
* `Cslib.Crypto.PRG.exists_secure_not_isSmallBias`: the counterexample to both printed claims.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of March 2007,
  Definition 8.20, Eq. (8.18), Exercises 8.25 and 8.38][Goldreich2007DraftR4]
-/

public section

namespace Cslib.Crypto.PRG

open Cslib.BitString Cslib.BranchingPrograms Cslib.Probability Finset
open Cslib.Probability.PMF
open scoped NNReal BigOperators

/-- Adding bits modulo `2` along a fold, in a state space `Fin w` with `w ≥ 2`, computes the sum of
the bits modulo `2`. -/
private theorem val_foldl_mod_two {w : ℕ} (hw : 2 ≤ w) :
    ∀ (L : ℕ) (f : Fin L → ℕ),
      ((Fin.foldl L (fun q t => (⟨((q : ℕ) + f t) % 2,
          (Nat.mod_lt _ two_pos).trans_le hw⟩ : Fin w)) (⟨0, by omega⟩ : Fin w) : Fin w) : ℕ) =
        (∑ t, f t) % 2
  | 0, _ => by simp
  | L + 1, f => by
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only
    rw [val_foldl_mod_two hw L, Nat.mod_add_mod]

/-- The read-once program of width `w ≥ 2` that computes the parity on `S`: its state is the
parity of the bits read so far in `S`. -/
private def parityProgram {L w : ℕ} (hw : 2 ≤ w) (S : Finset (Fin L)) :
    ReadOnceProgram L (Fin w) Bool where
  start := ⟨0, by omega⟩
  step t q b := ⟨((q : ℕ) + if t ∈ S ∧ b = true then 1 else 0) % 2,
    (Nat.mod_lt _ two_pos).trans_le hw⟩
  accept q := decide ((q : ℕ) = 1)

private theorem eval_parityProgram {L w : ℕ} (hw : 2 ≤ w) (S : Finset (Fin L))
    (x : Fin L → Bool) : (parityProgram hw S).eval x = parityOn S x := by
  have h := val_foldl_mod_two hw L fun t => if t ∈ S ∧ x t = true then 1 else 0
  rw [sum_boole, Nat.cast_id] at h
  simp only [ReadOnceProgram.eval, ReadOnceProgram.finalState, parityProgram, parityOn]
  have hS : ({t | t ∈ S ∧ x t = true} : Finset (Fin L)) = {i ∈ S | x i = true} := by
    ext; simp
  rw [h, hS]

/-- The parity of the bits in a set `S` of positions is a read-once test of every width `w ≥ 2`:
two states hold the parity of the bits read so far. -/
theorem isReadOnceTest_parityOn {L w : ℕ} (hw : 2 ≤ w) (S : Finset (Fin L)) :
    IsReadOnceTest w (fun x : Fin L → Bool => PMF.pure (parityOn S x)) :=
  ⟨parityProgram hw S, funext fun x => by rw [eval_parityProgram]⟩

/-- The average sign of a Boolean function is one minus twice its density. -/
private theorem expect_signVal {α : Type*} [Fintype α] [Nonempty α] (f : α → Bool) :
    𝔼 a, signVal (f a) = 1 - 2 * ((dens {a | f a = true} : ℚ≥0) : ℝ) := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h (a : α) : signVal (f a) = 1 - 2 * (if f a = true then 1 else 0 : ℝ) := by
    cases f a <;> norm_num [signVal]
  rw [Fintype.expect_eq_sum_div_card, nnratCast_dens]
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum, sum_boole]
  field_simp
  simp

/-- **Space-bounded pseudorandom generators are small-bias generators** ([Goldreich, Exercise
8.38][Goldreich2007DraftR4], corrected): a generator `G : {0,1}^k → {0,1}^ℓ` that fools the
read-once programs of width `2 ^ s`, `s ≥ 1`, with error `ε` is a `2ε`-bias generator. The printed
bound `ε` is false (`exists_secure_not_isSmallBias`). -/
theorem Generator.Secure.isSmallBias {k ℓ s : ℕ} {G : Generator (Fin k → Bool) (Fin ℓ → Bool)}
    {ε : ℝ≥0} (hs : 1 ≤ s) (hG : G.Secure (IsReadOnceTest (2 ^ s)) ε) :
    IsSmallBias (2 * ε) G.outputDist := by
  intro S hS
  have hw : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ s := Nat.pow_le_pow_right two_pos hs
  have h := hG _ (isReadOnceTest_parityOn hw S)
  rw [Generator.advantage, Generator.toReal_realExperiment_pure,
    Generator.toReal_idealExperiment_pure] at h
  -- The uniform distribution has odd parity on `S` with probability `1/2`.
  have hU : ((dens {y : Fin ℓ → Bool | parityOn S y = true} : ℚ≥0) : ℝ) = 1 / 2 := by
    have h0 := bias_uniformOfFintype (ι := Fin ℓ) S
    rw [ite_eq_right_iff.2 fun h => absurd h hS.ne_empty,
      ← PMF.map_id (PMF.uniformOfFintype (Fin ℓ → Bool)),
      bias_uniformOfFintype_map] at h0
    simp_rw [id, chi_eq_signVal_parityOn] at h0
    rw [expect_signVal] at h0
    linarith
  rw [Generator.outputDist, bias_uniformOfFintype_map]
  simp_rw [chi_eq_signVal_parityOn]
  rw [expect_signVal]
  rw [hU] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **The stretch of space-bounded pseudorandom generators** ([Goldreich, Exercise
8.25(2)][Goldreich2007DraftR4], corrected): a generator `G : {0,1}^k → {0,1}^ℓ` that fools the
read-once programs of width `2 ^ s`, `s ≥ 1`, with error `ε < 1/2` has `ℓ < 2^k`. The printed
hypothesis `ε < 1` does not suffice (`exists_secure_not_isSmallBias`). -/
theorem Generator.Secure.lt_two_pow {k ℓ s : ℕ} {G : Generator (Fin k → Bool) (Fin ℓ → Bool)}
    {ε : ℝ≥0} (hs : 1 ≤ s) (hε : (ε : ℝ) < 1 / 2) (hG : G.Secure (IsReadOnceTest (2 ^ s)) ε) :
    ℓ < 2 ^ k := by
  have h := card_lt_card_of_isSmallBias (by linarith) (hG.isSmallBias hs)
  simpa using h

/-- **Counterexample to the printed Exercises 8.38 and 8.25(2)** [Goldreich][Goldreich2007DraftR4]:
the generator `σ ↦ σσ` on one seed bit fools every test, however large its space, with error
`1/2`, but it is not `1/2`-biased (its two output bits always have even parity), and its stretch
is `2 = 2^1`. -/
theorem exists_secure_not_isSmallBias :
    ∃ G : Generator (Fin 1 → Bool) (Fin (2 ^ 1) → Bool),
      G.Secure (fun _ => True) (1 / 2) ∧ ¬ IsSmallBias (1 / 2) G.outputDist := by
  let G : Generator (Fin 1 → Bool) (Fin (2 ^ 1) → Bool) := ⟨fun σ _ => σ 0⟩
  -- Each output word has probability `1/2` (equal bits) or `0`, against `1/4` under uniform.
  have hcases : ∀ x : Fin (2 ^ 1) → Bool,
      #{σ : Fin 1 → Bool | (fun _ => σ 0 : Fin (2 ^ 1) → Bool) = x} = 1 ∨
        #{σ : Fin 1 → Bool | (fun _ => σ 0 : Fin (2 ^ 1) → Bool) = x} = 0 := by
    decide
  have hdist : dist G.outputDist (PMF.uniformOfFintype (Fin (2 ^ 1) → Bool)) = 1 / 2 := by
    rw [PMF.dist_eq]
    have hx (x : Fin (2 ^ 1) → Bool) : |(G.outputDist x).toReal -
        (PMF.uniformOfFintype (Fin (2 ^ 1) → Bool) x).toReal| = 1 / 4 := by
      rw [Generator.outputDist, toReal_uniformOfFintype_map_apply, PMF.uniformOfFintype_apply,
        nnratCast_dens]
      have hG : ⇑G = fun σ _ => σ 0 := rfl
      rw [hG]
      simp only [Fintype.card_pi, Fintype.card_bool, prod_const, card_univ, Fintype.card_fin,
        ENNReal.toReal_inv]
      rcases hcases x with h | h <;> rw [h] <;> norm_num
    simp only [hx, sum_const, card_univ, Fintype.card_pi, Fintype.card_bool, prod_const,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  refine ⟨G, fun A _ => ?_, fun hG => ?_⟩
  · have h := PMF.abs_bind_apply_toReal_sub_le_dist G.outputDist
      (PMF.uniformOfFintype (Fin (2 ^ 1) → Bool)) A true
    rw [hdist] at h
    rw [Generator.advantage]
    exact_mod_cast h
  · have h := hG univ univ_nonempty
    have hpar (σ : Fin 1 → Bool) : parityOn univ (G σ) = false := by
      revert σ; decide
    rw [Generator.outputDist, bias_uniformOfFintype_map] at h
    simp_rw [chi_eq_signVal_parityOn, hpar] at h
    rw [Finset.expect_const univ_nonempty] at h
    norm_num [signVal] at h

end Cslib.Crypto.PRG
