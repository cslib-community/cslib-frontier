/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle
public import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle.Computational
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT

/-!
# Tests for guessing advantage and random-oracle key derivation

Clients of `CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle` and
`CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle.Computational` under module
encapsulation, including hypothesis counterexample probes, nonvacuity of `SecretGuessHard`, and
concrete positive instances of Attack Game 8.3 and Theorem 8.10 ([BonehShoup2023], §8.10.1–8.10.2,
pp. 325–326 and 331–332, and §11.5.2 Attack Game 11.3, pp. 448–449).
-/

public section

namespace CslibFrontierTests.Crypto.RandomOracleKDF

open Cslib Probability Cslib.Crypto Cslib.Crypto.KeyDerivation Turing.MultiTapeTM
open Cslib.Probability.PMF (uniformOfFintype)
open scoped ENNReal NNReal

/-! ### 1. Probes for hypotheses and book comparisons -/

/-- **Probe 1 (non-constant `info` in `guessAdvantage_uniformOfFintype_const`)**: if `info` leaks
the secret (`info = id` on `Bool`), the adversary `pure` wins with probability `1 ≠ 2⁻¹`. -/
theorem guessAdvantage_uniformOfFintype_id_eq_one :
    guessAdvantage (uniformOfFintype Bool) id pure = 1 := by
  unfold guessAdvantage Game.succProbability
  have h : guessOutput (uniformOfFintype Bool) id pure true = 1 := by
    unfold guessOutput
    simp [ProbComp.eval_pure, PMF.pure_bind, PMF.bind_const]
  rw [h, ENNReal.toNNReal_one]

theorem guessAdvantage_uniformOfFintype_id_ne_inv :
    guessAdvantage (uniformOfFintype Bool) id pure ≠ (Fintype.card Bool : ℝ≥0)⁻¹ := by
  rw [guessAdvantage_uniformOfFintype_id_eq_one]
  simp [Fintype.card_bool]

/-- **Probe 2 (omitting the list-length bound `hB` in `listGuessAdvantage_le_mul_guessAdvantage`)**:
a list-guessing adversary returning `[false, true]` (length `2 > Q = 1`) wins on `Bool` with
probability `1`, whereas `1 * guessAdvantage ... (listGuessToGuess 1 _) = 2⁻¹`. -/
noncomputable def fullBoolListAdversary : ListGuessAdversary Unit Bool :=
  fun _ => pure [false, true]

theorem not_listGuessAdvantage_le_mul_of_length_gt :
    ¬ (listGuessAdvantage (uniformOfFintype Bool) (fun _ => ()) fullBoolListAdversary ≤
        (1 : ℕ) * guessAdvantage (uniformOfFintype Bool) (fun _ => ())
          (listGuessToGuess 1 fullBoolListAdversary)) := by
  rw [guessAdvantage_uniformOfFintype_const ()]
  have hlist : listGuessAdvantage (uniformOfFintype Bool) (fun _ => ())
      fullBoolListAdversary = 1 := by
    unfold listGuessAdvantage Game.succProbability
    have htrue : listGuessOutput (uniformOfFintype Bool) (fun _ => ())
        fullBoolListAdversary true = 1 := by
      unfold listGuessOutput fullBoolListAdversary
      simp [ProbComp.eval_pure, PMF.pure_bind, PMF.bind_const]
    rw [htrue, ENNReal.toNNReal_one]
  rw [hlist]
  simp [Fintype.card_bool]

/-- **Probe 3 (omitting `hQ : D.IsOracleQueryBounded Q` in `length_le_of_mem_support_roToListGuess`
and `roAdvantage_le_mul_guessAdvantage`)**: a distinguisher that queries the random oracle at
`false` (`1` query) violates both the `Q = 0` output-length bound and the `Q = 0` advantage
bound. -/
def queryFalseDistinguisher : RODistinguisher Unit Bool Bool :=
  fun _ t => do
    let y ← ProbOracleComp.query false
    return decide (y = t)

theorem queryFalseDistinguisher_isOracleQueryBounded_one :
    queryFalseDistinguisher.IsOracleQueryBounded 1 := by
  intro _ t
  simpa [queryFalseDistinguisher, ProbOracleComp.IsQueryBounded] using
    (ProbOracleComp.IsQueryBounded.query false).bind fun y =>
      OracleComp.IsCostBounded.pure (decide (y = t)) 0

theorem mem_support_roToListGuess_queryFalseDistinguisher :
    [false] ∈ (ProbComp.eval (roToListGuess queryFalseDistinguisher ())).support ∧
      ¬ ([false].length ≤ 0) := by
  refine ⟨?_, by decide⟩
  have hlog : (queryFalseDistinguisher () false).runLog (fun _ => pure false) =
      pure (true, [(false, false)]) := by
    simp only [queryFalseDistinguisher, ProbOracleComp.runLog, ProbOracleComp.runState_bind,
      ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind,
      StateT.run_pure]
    simp [StateT.run]
  simp only [roToListGuess, ProbComp.eval_bind, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff]
  refine ⟨fun _ => false, by simp [uniformOfFintype], false,
    by simp [uniformOfFintype], ?_⟩
  simp [hlog]

theorem roAdvantage_queryFalseDistinguisher_pure_eq_half :
    roAdvantage (PMF.pure false) (fun _ => ()) queryFalseDistinguisher = 2⁻¹ := by
  have hrun (table : Bool → Bool) (t : Bool) :
      ProbComp.eval ((queryFalseDistinguisher () t).run fun q => pure (table q)) =
        PMF.pure (decide (table false = t)) := by
    simp [queryFalseDistinguisher]
  have hreal : roRealOutput (PMF.pure false) (fun _ => ()) queryFalseDistinguisher true = 1 := by
    unfold roRealOutput realOutput
    simp [hrun, PMF.bind_const]
  have hideal :
      roIdealOutput (PMF.pure false) (fun _ => ()) queryFalseDistinguisher true = 2⁻¹ := by
    unfold roIdealOutput idealOutput
    simp only [PMF.pure_bind, hrun]
    rw [PMF.bind_apply]
    have hpt (table : Bool → Bool) :
        ((uniformOfFintype Bool).bind fun z => PMF.pure (decide (table false = z))) true = 2⁻¹ := by
      rw [Probability.PMF.bind_pure_decide_eq_apply_true, PMF.uniformOfFintype_apply,
        Fintype.card_bool]
      norm_num
    simp only [hpt, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [← NNReal.coe_inj, roAdvantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability, hreal, hideal]
  norm_num

theorem not_roAdvantage_le_mul_of_not_queryBounded :
    ¬ (roAdvantage (PMF.pure false) (fun _ => ()) queryFalseDistinguisher ≤
        (0 : ℕ) * guessAdvantage (PMF.pure false) (fun _ => ())
          (roToGuess 0 queryFalseDistinguisher)) := by
  rw [roAdvantage_queryFalseDistinguisher_pure_eq_half]
  norm_num

/-! ### 2. Concrete positive instances for callers -/

/-- **Test 1**: Any distinguisher that makes `0` random-oracle queries has zero ROM KDF
distinguishing advantage. -/
theorem roAdvantage_eq_zero_of_isOracleQueryBounded_zero {X S T : Type} [Fintype S]
    [DecidableEq S] [Nonempty S] [Fintype T] [Nonempty T] (sample : PMF S) (info : S → X)
    {D : RODistinguisher X S T} (hD : D.IsOracleQueryBounded 0) :
    roAdvantage sample info D = 0 :=
  nonpos_iff_eq_zero.mp (by simpa using roAdvantage_le_mul_guessAdvantage sample info hD)

/-- **Test 2**: On a uniform secret in `Bool` with no leakage, the 1-query distinguisher
`queryFalseDistinguisher` has ROM KDF advantage at most `2⁻¹`. -/
theorem roAdvantage_queryFalseDistinguisher_uniform_le :
    roAdvantage (uniformOfFintype Bool) (fun _ => ()) queryFalseDistinguisher ≤ 2⁻¹ := by
  have h := roAdvantage_le_mul_guessAdvantage (uniformOfFintype Bool) (fun _ => ())
    queryFalseDistinguisher_isOracleQueryBounded_one
  rw [guessAdvantage_uniformOfFintype_const ()] at h
  simpa [Fintype.card_bool] using h

/-- **Test 3 ([BonehShoup2023], §8.10.1 third example, pp. 325–326, and Theorem 8.10, p. 331)**:
For a uniform 128-bit secret (`BitString (64 + 64)`) with its first 64 bits leaked:
(a) every guessing adversary has guessing advantage at most `1 / 2 ^ 64`;
(b) every `Q`-query random-oracle KDF distinguisher has advantage at most `Q * (1 / 2 ^ 64)`. -/
theorem guessAdvantage_bitString128_take64_le
    (A : GuessAdversary (BitString 64) (BitString (64 + 64))) :
    guessAdvantage (uniformOfFintype (BitString (64 + 64)))
      (Fin.take 64 (Nat.le_add_right 64 64)) A ≤ 1 / 2 ^ 64 :=
  guessAdvantage_uniformOfFintype_take_le 64 64 A

/-- **Test 3a ([BonehShoup2023], §8.10.1 third example, pp. 325–326)**: applying
`guessAdvantage_le_card_mul_of_mass_le` directly to the uniform 128-bit secret with 64 bits
leaked (`|BitString 64| * 2⁻¹²⁸ = 2⁻⁶⁴`). -/
theorem guessAdvantage_bitString128_take64_le_of_mass_le
    (A : GuessAdversary (BitString 64) (BitString (64 + 64))) :
    guessAdvantage (uniformOfFintype (BitString (64 + 64)))
      (Fin.take 64 (Nat.le_add_right 64 64)) A ≤ 1 / 2 ^ 64 := by
  have h := guessAdvantage_le_card_mul_of_mass_le
    (uniformOfFintype (BitString (64 + 64))) (Fin.take 64 (Nat.le_add_right 64 64))
    (mass := (2 ^ 128 : ℝ≥0)⁻¹) (fun s => by
      simp [PMF.uniformOfFintype_apply, BitString]
      norm_num) A
  refine h.trans_eq ?_
  have hcard : Fintype.card (BitString 64) = 2 ^ 64 := by
    simp [BitString, Fintype.card_pi]
  rw [hcard]
  norm_num

theorem roAdvantage_bitString128_take64_le {T : Type} [Fintype T] [Nonempty T]
    {D : RODistinguisher (BitString 64) (BitString (64 + 64)) T} {Q : ℕ}
    (hQ : D.IsOracleQueryBounded Q) :
    roAdvantage (uniformOfFintype (BitString (64 + 64)))
      (Fin.take 64 (Nat.le_add_right 64 64)) D ≤ Q * (1 / 2 ^ 64) :=
  (roAdvantage_le_mul_guessAdvantage _ _ hQ).trans
    (mul_le_mul' le_rfl (guessAdvantage_bitString128_take64_le (roToGuess Q D)))

/-- **Test 4 ([BonehShoup2023], §8.10.2, p. 331, and §11.5.2 Attack Game 11.3, pp. 448–449)**:
on the family of uniform `(n + n)`-bit secrets with the first `n` bits leaked, every polynomially
query-bounded family of random-oracle KDF distinguishers has negligible distinguishing advantage. -/
theorem negligible_roAdvantage_bitString_take {T : ℕ → Type}
    [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {D : ∀ n, RODistinguisher (BitString n) (BitString (n + n)) (T n)} {Q : ℕ → ℕ}
    (hQ : PolynomiallyBounded Q) (hD : ∀ n, (D n).IsOracleQueryBounded (Q n)) :
    Negligible fun n =>
      roAdvantage (uniformOfFintype (BitString (n + n)))
        (Fin.take n (Nat.le_add_right n n)) (D n) := by
  refine negligible_roAdvantage_of_negligible_guessAdvantage
    (fun n => uniformOfFintype (BitString (n + n)))
    (fun n => Fin.take n (Nat.le_add_right n n)) hQ hD ?_
  exact fun A => negligible_of_le negligible_one_div_two_pow fun n => by
    simpa using guessAdvantage_uniformOfFintype_take_le n n (A n)

/-- **Test 5**: `maxPosteriorGuess` relation on a non-uniform secret on `Bool`: a secret biased
toward `true` (mass `3/4` on `true`, `1/4` on `false`) with constant side information bounds
every randomized guessing adversary's advantage via
`guessAdvantage_le_one_sub_errorProb_maxPosteriorGuess`, achieved by `fun _ => pure true`. -/
noncomputable def biasedBool : PMF Bool :=
  (uniformOfFintype (Fin 4)).map fun i => decide (i.1 < 3)

theorem biasedBool_apply_true : biasedBool true = 3 / 4 := by
  simp only [biasedBool, PMF.map_apply, tsum_fintype, Fin.sum_univ_four,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num
  rw [div_eq_mul_inv]
  ring

theorem biasedBool_apply_false : biasedBool false = 1 / 4 := by
  simp only [biasedBool, PMF.map_apply, tsum_fintype, Fin.sum_univ_four,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num

theorem conditionalSnd_biasedBool (b : Bool) :
    Probability.PMF.conditionalSnd (biasedBool.map fun s => ((), s)) () b = biasedBool b := by
  have hm : (biasedBool.map fun s => ((), s)).map Prod.fst = PMF.pure () := by
    rw [PMF.map_comp]
    ext x
    simp
  rw [Probability.PMF.conditionalSnd_apply _ () (by simp [hm]), hm]
  simp [PMF.map_apply]

theorem maxPosteriorGuess_biasedBool :
    Probability.PMF.maxPosteriorGuess (biasedBool.map fun s => ((), s)) () = true := by
  have hle := Probability.PMF.conditionalSnd_le_conditionalSnd_maxPosteriorGuess
    (biasedBool.map fun s => ((), s)) () true
  rw [conditionalSnd_biasedBool, conditionalSnd_biasedBool, biasedBool_apply_true] at hle
  cases h : Probability.PMF.maxPosteriorGuess (biasedBool.map fun s => ((), s)) ()
  · rw [h, biasedBool_apply_false] at hle
    have hreal := ENNReal.toReal_mono (by simp) hle
    norm_num at hreal
  · rfl

theorem guessAdvantage_biasedBool_le (A : GuessAdversary Unit Bool) :
    (guessAdvantage biasedBool (fun _ => ()) A : ℝ) ≤ 3 / 4 := by
  have h := guessAdvantage_le_one_sub_errorProb_maxPosteriorGuess biasedBool (fun _ => ()) A
  have herr :
      ((biasedBool.map fun s => ((), s)).toOuterMeasure
        {z | Probability.PMF.maxPosteriorGuess (biasedBool.map fun s => ((), s)) z.1 ≠
          z.2}).toReal = 1 / 4 := by
    have hset :
        {z : Unit × Bool |
          Probability.PMF.maxPosteriorGuess (biasedBool.map fun s => ((), s)) z.1 ≠ z.2} =
          {((), false)} := by
      ext ⟨u, b⟩
      cases u
      cases b <;> simp [maxPosteriorGuess_biasedBool]
    rw [hset, PMF.toOuterMeasure_apply_singleton]
    have hpt : (biasedBool.map fun s => ((), s)) ((), false) = 1 / 4 := by
      rw [PMF.map_apply]
      simpa using biasedBool_apply_false
    simp [hpt]
  linarith

theorem guessAdvantage_biasedBool_pure_true :
    guessAdvantage biasedBool (fun _ => ()) (fun _ => pure true) = 3 / 4 := by
  unfold guessAdvantage Game.succProbability
  rw [guessOutput_pure_apply_true]
  have hset :
      {z : Unit × Bool | (fun _ : Unit => true) z.1 = z.2} = {((), true)} := by
    ext ⟨u, b⟩
    cases u
    cases b <;> simp
  rw [hset, PMF.toOuterMeasure_apply_singleton]
  have hpt : (biasedBool.map fun s => ((), s)) ((), true) = 3 / 4 := by
    rw [PMF.map_apply]
    simpa using biasedBool_apply_true
  rw [hpt, ← ENNReal.coe_inj, ENNReal.coe_toNNReal (by finiteness)]
  push_cast
  rfl

/-! ### 3. Computational unpredictability (`SecretGuessHard`) and lazy Theorem 8.10 -/

/-- Echo guesser for `not_secretGuessHard_echo`: reads the leaked bit list as an `n`-bit string. -/
def echoGuessAdversary : GuessFamilyAdversary (List Bool) id :=
  fun n w => pure (BitString.ofList n w)

theorem isPPT_echoGuessAdversary : echoGuessAdversary.IsPPT encBits := by
  let E := encPair encUnary encBits
  have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) E encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun p : ℕ × List Bool => p.2) E encBits := by fun_prop
  have hpad : ComputableInPolyTime (fun p : ℕ × List Bool => List.replicate p.1 false) E encBits :=
    (bits_encList_polyTime encBool).2.comp
      (ComputableInPolyTime.replicate hn (ComputableInPolyTime.const false))
  have hslice : ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.2 ++ List.replicate p.1 false).take p.1) E encBits := by
    have hn' := hn.tidy
    have hw' := hw.tidy
    have hpad' := hpad.tidy
    exact .of_tidy (by fun_prop)
  refine hslice.isPPTOn.congr fun p => ?_
  simp only [echoGuessAdversary, id_eq, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map,
    BitString.ofFn_ofList_eq_take]

/-- **Nonvacuity (`not_secretGuessHard_echo`)**: when `info n s = List.ofFn s` leaks the entire
`n`-bit secret, `echoGuessAdversary` is uniform strict PPT and wins with probability `1`, refuting
`SecretGuessHard`. -/
theorem not_secretGuessHard_echo :
    ¬ SecretGuessHard encBits id (fun n => uniformOfFintype (BitString n))
        (fun _ s => List.ofFn s) := by
  intro h
  refine not_negligible_const (c := 1) (by norm_num)
    ((h echoGuessAdversary isPPT_echoGuessAdversary).congr fun n => ?_)
  dsimp only [id_eq]
  unfold guessAdvantage Game.succProbability
  have htrue : guessOutput (uniformOfFintype (BitString n)) (fun s => List.ofFn s)
      (echoGuessAdversary n) true = 1 := by
    unfold guessOutput echoGuessAdversary
    simp [ProbComp.eval_pure, PMF.pure_bind, PMF.bind_const]
  rw [htrue, ENNReal.toNNReal_one]

/-- **Satisfying instance (`secretGuessHard_uniform_unit`)**: a uniform `n`-bit secret with no side
information (`info n _ = ()`) satisfies `SecretGuessHard`. -/
theorem secretGuessHard_uniform_unit :
    SecretGuessHard encUnit id (fun n => uniformOfFintype (BitString n)) (fun _ _ => ()) := by
  intro A _
  refine negligible_of_le negligible_one_div_two_pow fun n => ?_
  dsimp only [id_eq]
  rw [guessAdvantage_uniformOfFintype_const ()]
  have hcard : Fintype.card (BitString n) = 2 ^ n := by simp [BitString, Fintype.card_pi]
  simp [hcard, one_div]

/-- **Positive end-to-end application of computational Theorem 8.10**: on a uniform `n`-bit secret
with no side information, every uniform strict oracle-PPT word distinguisher has negligible
random-oracle KDF distinguishing advantage for any unary-poly-time `outLen`. -/
theorem negligible_roAdvantage_uniform_unit {outLen : ℕ → ℕ}
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    {D : WordRODistinguisher Unit} (hD : D.IsPPT encUnit) :
    Negligible fun n =>
      roAdvantage (uniformOfFintype (BitString n)) (fun _ => ())
        (toRODistinguisher id outLen D n) :=
  secretGuessHard_uniform_unit.negligible_roAdvantage .id' hout
    ⟨0, 0, fun _ _ _ => by simp [encUnit]; rfl⟩ hD

/-- **Satisfying instance with growing side information** ([BonehShoup2023], §8.10.1 third example,
pp. 325–326, and Theorem 8.10, pp. 331–332): on a uniform `(n + n)`-bit secret leaking its first `n`
bits as `List Bool`, `SecretGuessHard` holds and `SecretGuessHard.negligible_roAdvantage` yields
negligible random-oracle KDF advantage for every uniform strict oracle-PPT word distinguisher. -/
theorem secretGuessHard_bitString_take :
    SecretGuessHard encBits (fun n => n + n)
      (fun n => uniformOfFintype (BitString (n + n)))
      (fun n s => List.ofFn (Fin.take n (Nat.le_add_right n n) s)) := by
  intro A _
  refine negligible_of_le negligible_one_div_two_pow fun n => ?_
  have heq : guessAdvantage (uniformOfFintype (BitString (n + n)))
      (fun s => List.ofFn (Fin.take n (Nat.le_add_right n n) s)) (A n) =
      guessAdvantage (uniformOfFintype (BitString (n + n)))
        (Fin.take n (Nat.le_add_right n n)) (fun p => A n (List.ofFn p)) := rfl
  dsimp only
  rw [heq]
  simpa using guessAdvantage_uniformOfFintype_take_le n n (fun p => A n (List.ofFn p))

theorem negligible_roAdvantage_word_bitString_take {outLen : ℕ → ℕ}
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    {D : WordRODistinguisher (List Bool)} (hD : D.IsPPT encBits) :
    Negligible fun n =>
      roAdvantage (uniformOfFintype (BitString (n + n)))
        (fun s => List.ofFn (Fin.take n (Nat.le_add_right n n) s))
        (toRODistinguisher (fun n => n + n) outLen D n) :=
  secretGuessHard_bitString_take.negligible_roAdvantage
    (.of_tidy (by fun_prop)) hout ⟨1, 1, fun n _ _ => by simp⟩ hD

end CslibFrontierTests.Crypto.RandomOracleKDF
