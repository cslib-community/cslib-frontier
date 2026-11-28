/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect

/-!
# Security against guessing Internet roulette outcomes

Semantic security gives security for single-zero Internet roulette (`Fin 37`, outcomes `0..36`)
([BonehShoup2023], Section 2.2.4, pp. 22–25). The book defines four even-money bets (`high`,
`low`, `even`, `odd`, p. 22); `RouletteBet` includes those four and adds `red` and `black`,
making the universal statements over all players stronger. Each bet wins on `18` nonzero
wheel outcomes and loses on `0` and the remaining `18` outcomes, so an adversary betting against an
encrypted wheel outcome has concrete Internet roulette advantage
`nndist Pr[W(r, bet) = 1] (18 / 37)` (`|Pr[W(r, bet) = 1] - 18 / 37|`, p. 22).

In the concrete single-cipher model (`Cipher.oneTimeExperiment`), the explicit `TwoStage` reduction
`rouletteReduction` asks to distinguish a uniform `r : Fin 37` from `0`, equating the roulette
advantage with the semantic-security distinguishing advantage whenever `valid` admits every pair
`(r, 0)` on `Fin 37` (`rouletteAdvantage_eq_advantage_rouletteReduction`, capturing (2.7) and (2.8)
on p. 23, and cf. (2.9) on p. 25; without an efficiency claim). The hypothesis
`∀ r : Fin 37, valid r 0 = true` is required because `Cipher.oneTimeExperiment` rejects pairs where
`valid` returns `false`, whereas Attack Game 2.1 admits every fixed-size message pair on `Fin 37`.

In the uniform asymptotic `DEMOneTimeKeyINDCPAOf` model (`keyLen`, `encryptSym`),
`rouletteToDEMAdversary` uses `rouletteReduction` with modular residue sampling
`ProbComp.sampleModNat (width n) 37` in place of exact uniform `Fin 37` sampling, saving the residue
encoded in unary length in the adversary state (`isPPT_rouletteToDEMAdversary`). Consequently,
`rouletteDEMAdvantage_le_demKeyGame_add` incurs a `(74 : ℝ≥0) / 2 ^ width n` statistical-distance
overhead (one `37 / 2 ^ width n` term on each side of the two-experiment bound) where the book has
an equality. Fixing `width := id` internally,
`DEMOneTimeKeyINDCPAOf.negligible_rouletteDEMAdvantage` proves Theorem 2.9 (p. 23):
`rouletteDEMAdvantage keyLen encryptSym A` is negligible for every uniform strict PPT adversary
`A : ℕ → List Bool → ProbComp RouletteBet`.

## Main definitions

* `Cslib.Crypto.Encryption.RouletteBet`, `Cslib.Crypto.Encryption.rouletteWin`: the four book
  even-money bets (`even`, `odd`, `low`, `high`) plus `red` and `black` on `Fin 37`, and the
  winning predicate `W(r, bet)`.
* `Cslib.Crypto.Encryption.rouletteExperiment`,
  `Cslib.Crypto.Encryption.idealRouletteExperiment`, `Cslib.Crypto.Encryption.rouletteAdvantage`:
  the real and ideal roulette experiments and concrete roulette advantage.
* `Cslib.Crypto.Encryption.rouletteReduction`: the parameterized `TwoStage` semantic-security
  reduction.
* `Cslib.Crypto.Encryption.rouletteDEMExperiment`,
  `Cslib.Crypto.Encryption.rouletteDEMAdvantage`, `Cslib.Crypto.Encryption.rouletteToDEMAdversary`:
  the parameterized DEM-style roulette experiment, advantage defined from it, and uniform adversary
  reduction.

## Main results

* `Cslib.Crypto.Encryption.succProbability_uniform_rouletteWin`: each bet wins with probability
  `18 / 37` under uniform `Fin 37`.
* `Cslib.Crypto.Encryption.succProbability_idealRouletteExperiment`: the ideal roulette experiment
  wins with probability `18 / 37`.
* `Cslib.Crypto.Encryption.rouletteAdvantage_eq_advantage_rouletteReduction`: display (2.7) (p. 23).
* `Cslib.Crypto.Encryption.isPPT_rouletteToDEMAdversary`: strict uniform PPT certification of
  `rouletteToDEMAdversary`.
* `Cslib.Crypto.Encryption.rouletteDEMAdvantage_le_demKeyGame_add`: concrete DEM reduction bound.
* `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOf.negligible_rouletteDEMAdvantage`: asymptotic
  Theorem 2.9 from `DEMOneTimeKeyINDCPAOf`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 2.2.4 (pp. 22–25), Theorem 2.9 (p. 23).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Even-money bets on a 37-pocket single-zero roulette wheel `Fin 37` ([BonehShoup2023],
Section 2.2.4, p. 22). Includes the book's four bets (`even`, `odd`, `low`, `high`) together with
the additional bets `red` and `black`; each wins on `18` nonzero outcomes and loses on `0` and the
remaining `18` outcomes. -/
inductive RouletteBet : Type where
  | red
  | black
  | even
  | odd
  | low
  | high
  deriving DecidableEq, Inhabited

instance : Fintype RouletteBet :=
  ⟨{.red, .black, .even, .odd, .low, .high}, fun x => by cases x <;> decide⟩

/-- Winning predicate `W(r, bet)` for European roulette outcome `r : Fin 37` and bet
`bet : RouletteBet` ([BonehShoup2023], Section 2.2.4, p. 22). Outcome `0` always loses. -/
@[expose] def rouletteWin (r : Fin 37) (bet : RouletteBet) : Bool :=
  let redPockets : Finset ℕ :=
    {1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36}
  match bet with
  | .red => decide (r.val ∈ redPockets)
  | .black => decide (r.val ≠ 0 ∧ r.val ∉ redPockets)
  | .even => decide (r.val ≠ 0 ∧ r.val % 2 = 0)
  | .odd => decide (r.val % 2 = 1)
  | .low => decide (1 ≤ r.val ∧ r.val ≤ 18)
  | .high => decide (19 ≤ r.val)

/-- Under a uniform wheel spin `r : Fin 37`, every `RouletteBet` wins with probability `18 / 37`. -/
theorem succProbability_uniform_rouletteWin (bet : RouletteBet) :
    (Game.succProbability ((PMF.uniformOfFintype (Fin 37)).map
      fun r => rouletteWin r bet) : ℝ) = 18 / 37 := by
  change (((PMF.uniformOfFintype (Fin 37)).map (fun r => rouletteWin r bet)) true).toReal =
    18 / 37
  rw [Probability.PMF.toReal_uniformOfFintype_map_apply_true, Finset.dens_eq_card_div_card]
  have hcard : ({r : Fin 37 | rouletteWin r bet = true} : Finset (Fin 37)).card = 18 := by
    cases bet <;> decide
  rw [hcard, Fintype.card_fin]
  norm_num

/-- Real Internet roulette experiment: spin a uniform wheel outcome `r : Fin 37`, sample a fresh
key `k ← sampleKey`, encrypt `r`, and test `rouletteWin r bet` on the adversary's bet
([BonehShoup2023], Section 2.2.4, p. 22). -/
@[expose] noncomputable def rouletteExperiment {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    (A : C → ProbComp RouletteBet) : Experiment := do
  let r ← ProbComp.uniform (Fin 37)
  let k ← sampleKey
  let ct ← E.encrypt k r
  let bet ← A ct
  pure (rouletteWin r bet)

/-- Ideal Internet roulette experiment: spin `r : Fin 37`, pass an encryption of the fixed outcome
`0` to the adversary, and test `rouletteWin r bet` ([BonehShoup2023], Section 2.2.4, p. 23). -/
@[expose] noncomputable def idealRouletteExperiment {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    (A : C → ProbComp RouletteBet) : Experiment := do
  let r ← ProbComp.uniform (Fin 37)
  let k ← sampleKey
  let ct ← E.encrypt k 0
  let bet ← A ct
  pure (rouletteWin r bet)

/-- In `idealRouletteExperiment`, the ciphertext reveals nothing about `r`, so any adversary wins
with probability `18 / 37`. -/
theorem succProbability_idealRouletteExperiment {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    (A : C → ProbComp RouletteBet) :
    Pr[idealRouletteExperiment E sampleKey A] = 18 / 37 := by
  have heval :
      ProbComp.eval (idealRouletteExperiment E sampleKey A) =
        (ProbComp.eval (sampleKey >>= fun k => E.encrypt k 0 >>= A)).bind fun bet =>
          (PMF.uniformOfFintype (Fin 37)).map fun r => rouletteWin r bet := by
    simp only [idealRouletteExperiment, ← bind_assoc, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure]
    rw [PMF.bind_comm]
    rfl
  have htrue :
      (ProbComp.eval (idealRouletteExperiment E sampleKey A)) true =
        ENNReal.ofReal (18 / 37) := by
    rw [heval]
    refine Probability.PMF.bind_apply_of_forall _ fun bet => ?_
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ true)]
    exact congrArg ENNReal.ofReal (succProbability_uniform_rouletteWin bet)
  have hnn : (0 : ℝ) ≤ 18 / 37 := by norm_num
  change ((ProbComp.eval (idealRouletteExperiment E sampleKey A)) true).toReal = 18 / 37
  rw [htrue, ENNReal.toReal_ofReal hnn]

/-- Internet roulette advantage `IRadv[A] := |Pr[W(r, bet) = 1] - 18 / 37|` ([BonehShoup2023],
Section 2.2.4, p. 22), packaged as a nonnegative real via `nndist`. -/
@[expose] noncomputable def rouletteAdvantage {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    (A : C → ProbComp RouletteBet) : ℝ≥0 :=
  nndist Pr[rouletteExperiment E sampleKey A] (18 / 37 : ℝ)

private theorem rouletteAdvantage_eq_advantage_ideal {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    (A : C → ProbComp RouletteBet) :
    rouletteAdvantage E sampleKey A =
      Experiment.advantage (rouletteExperiment E sampleKey A)
        (idealRouletteExperiment E sampleKey A) := by
  apply NNReal.eq
  rw [rouletteAdvantage, coe_nndist, Real.dist_eq, Experiment.coe_advantage,
    succProbability_idealRouletteExperiment]

/-- Explicit `TwoStage` semantic-security reduction for Internet roulette, parameterized by the
challenge index sampler `sampleIndex` ([BonehShoup2023], Section 2.2.4, p. 23): choose `(r, 0)`
with `r ← sampleIndex` and save `r`, then on challenge ciphertext `ct` run `A ct` and return
`rouletteWin r bet`. -/
@[expose] noncomputable def rouletteReduction {C : Type}
    (sampleIndex : ProbComp (Fin 37)) (A : C → ProbComp RouletteBet) :
    TwoStage Unit (MessagePair (Fin 37)) C Bool (Fin 37) where
  choose _ := do
    let r ← sampleIndex
    pure (⟨r, 0⟩, r)
  guess r ct := do
    let bet ← A ct
    pure (rouletteWin r bet)

private theorem eval_oneTimeExperiment_rouletteReduction {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    {valid : Fin 37 → Fin 37 → Bool} (hvalid : ∀ r : Fin 37, valid r 0 = true)
    (A : C → ProbComp RouletteBet) (b : Bool) :
    ProbComp.eval (E.oneTimeExperiment sampleKey valid
      (rouletteReduction (ProbComp.uniform (Fin 37)) A) b) =
      ProbComp.eval (if b then idealRouletteExperiment E sampleKey A
        else rouletteExperiment E sampleKey A) := by
  simp only [Cipher.oneTimeExperiment, lrExperiment, rouletteReduction,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind]
  rw [PMF.bind_comm]
  cases b <;>
    simp [idealRouletteExperiment, rouletteExperiment, ProbComp.eval_bind, PMF.map,
      Function.comp_def, hvalid]

/-- Display (2.7) ([BonehShoup2023], Section 2.2.4, p. 23, and cf. (2.8)): whenever `valid` admits
every pair `(r, 0)` on `Fin 37`, `rouletteAdvantage` equals the semantic-security distinguishing
advantage of `rouletteReduction (ProbComp.uniform (Fin 37)) A`. -/
theorem rouletteAdvantage_eq_advantage_rouletteReduction {K C : Type}
    (E : Cipher K (Fin 37) C) (sampleKey : ProbComp K)
    {valid : Fin 37 → Fin 37 → Bool} (hvalid : ∀ r : Fin 37, valid r 0 = true)
    (A : C → ProbComp RouletteBet) :
    rouletteAdvantage E sampleKey A =
      Experiment.advantage
        (E.oneTimeExperiment sampleKey valid
          (rouletteReduction (ProbComp.uniform (Fin 37)) A) false)
        (E.oneTimeExperiment sampleKey valid
          (rouletteReduction (ProbComp.uniform (Fin 37)) A) true) := by
  rw [rouletteAdvantage_eq_advantage_ideal]
  simp [Experiment.advantage, eval_oneTimeExperiment_rouletteReduction E sampleKey hvalid A]

/-! ### Uniform asymptotic DEM reduction -/

/-- Parameterized symmetric-cipher Internet roulette experiment using a `keyLen n`-bit key and
`encryptSym n` via `wordCipher`. -/
@[expose] noncomputable def rouletteDEMExperiment (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (n : ℕ) : Experiment :=
  rouletteExperiment (wordCipher encryptSym (fun _ _ _ => none) n)
    (BitString.sampleList (keyLen n)) (A n)

/-- Parameterized symmetric-cipher Internet roulette advantage `|Pr[W(r, bet) = 1] - 18 / 37|`,
defined directly through `rouletteDEMExperiment`. -/
@[expose] noncomputable def rouletteDEMAdvantage (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (n : ℕ) : ℝ≥0 :=
  nndist Pr[rouletteDEMExperiment keyLen encryptSym A n] (18 / 37 : ℝ)

/-- Word-level `AdversaryOf (Fin 37)` wrapper around `rouletteReduction`: phase 1 invokes
`rouletteReduction` with `sampleModNat (width n) 37` and stores `r.val` in the unary state length;
phase 2 recovers `r` from `state.length % 37`, runs `A n ct`, and evaluates `rouletteWin`. -/
@[expose] noncomputable def rouletteToDEMAdversary (width : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp RouletteBet) : AdversaryOf (Fin 37) where
  choose n _ := do
    let choice ← (rouletteReduction
      (ProbComp.sampleModNat (width n) 37 >>= fun x =>
        pure ⟨x % 37, Nat.mod_lt _ (by decide)⟩) (A n)).choose ()
    pure ((choice.1.msg₀, choice.1.msg₁), encUnary choice.2.val)
  guess n state ct := do
    let bet ← A n ct
    pure (rouletteWin ⟨state.length % 37, Nat.mod_lt _ (by decide)⟩ bet)

private theorem isPPT_rouletteToDEMAdversary_choose {encIndex : Fin 37 ↪ List Bool}
    {width : ℕ → ℕ} (hwidth : ComputableInPolyTime width encUnary encUnary)
    (A : ℕ → List Bool → ProbComp RouletteBet) :
    Probability.IsPPT (encChoiceOut encIndex)
      (rouletteToDEMAdversary width A).choose := by
  have hsample :
      IsPPTOn (encPair encUnary encBits) encNat
        (fun p : ℕ × List Bool => ProbComp.sampleModNat (width p.1) 37) :=
    isPPTOn_sampleModNat (hwidth.comp (ComputableInPolyTime.fst encUnary encBits))
      (ComputableInPolyTime.const 37)
  have hmod_unary :
      ComputableInPolyTime (fun x : ℕ => x % 37) encNat encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_mod.comp
        (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 37)))
      (ComputableInPolyTime.const 36) (fun x => by omega)
  have hfin :
      ComputableInPolyTime
        (fun x : ℕ => (⟨x % 37, Nat.mod_lt _ (by decide)⟩ : Fin 37))
        encNat encIndex :=
    ((ComputableInPolyTime.unary_finMod (by decide : 0 < 37) encIndex).comp hmod_unary).of_enc_eq
      (fun x => congrArg encIndex (Fin.ext (Nat.mod_mod x 37).symm))
  exact IsPPTOn.isPPT (by
    simpa [rouletteToDEMAdversary, rouletteReduction, bind_assoc, pure_bind,
      Function.comp_def] using hsample.map
        ((ComputableInPolyTime.of_finite (encOut := encChoiceOut encIndex)
          fun r : Fin 37 => ((r, (0 : Fin 37)), encUnary r.val)).comp hfin))

private theorem isPPT_rouletteToDEMAdversary_guess (width : ℕ → ℕ)
    {encBet : RouletteBet ↪ List Bool}
    {A : ℕ → List Bool → ProbComp RouletteBet} (hA : Probability.IsPPT encBet A) :
    IsPPTOn encGuessInput encBool
      (fun p => (rouletteToDEMAdversary width A).guess p.1 p.2.1 p.2.2) := by
  let encFin37 : Fin 37 ↪ List Bool := encFinite (Fin 37)
  have hfirst :
      IsPPTOn encGuessInput encBet (fun p : ℕ × List Bool × List Bool => A p.1 p.2.2) :=
    hA.on.preprocess (prepare := fun p : ℕ × List Bool × List Bool => (p.1, p.2.2)) (by fun_prop)
  have hidx :
      ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × RouletteBet =>
          (⟨p.1.2.1.length % 37, Nat.mod_lt _ (by decide)⟩ : Fin 37))
        (encPair encGuessInput encBet) encFin37 :=
    (ComputableInPolyTime.unary_finMod (by decide : 0 < 37) encFin37).comp
      (ComputableInPolyTime.length_bits_comp (by fun_prop))
  simpa [rouletteToDEMAdversary] using hfirst.map_with
    ((ComputableInPolyTime.of_finite (encOut := encBool)
      fun q : Fin 37 × RouletteBet => rouletteWin q.1 q.2).comp (hidx.prod (by fun_prop)))

/-- Whenever `width` is polynomial-time computable in unary and `A` is uniform strict PPT,
`rouletteToDEMAdversary width A` is a uniform strict PPT `AdversaryOf (Fin 37)`. -/
theorem isPPT_rouletteToDEMAdversary {encIndex : Fin 37 ↪ List Bool}
    {encBet : RouletteBet ↪ List Bool} {width : ℕ → ℕ}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    {A : ℕ → List Bool → ProbComp RouletteBet} (hA : Probability.IsPPT encBet A) :
    AdversaryOf.IsPPT encIndex (rouletteToDEMAdversary width A) where
  choose := isPPT_rouletteToDEMAdversary_choose hwidth A
  guess := isPPT_rouletteToDEMAdversary_guess width hA

private noncomputable def rouletteModGame (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (n : ℕ) (b : Bool) (x : ℕ) : Game :=
  ProbComp.eval do
    let k ← BitString.sampleList (keyLen n)
    let r : Fin 37 := ⟨x % 37, Nat.mod_lt _ (by decide)⟩
    let ct ← encryptSym n k (if b then 0 else r)
    let bet ← A n ct
    pure (rouletteWin r bet)

private theorem eval_demKeyGame_rouletteToDEMAdversary (width keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (b : Bool) (n : ℕ) :
    ProbComp.eval
        (demKeyGame keyLen encryptSym (rouletteToDEMAdversary width A) b n) =
      (ProbComp.eval (ProbComp.sampleModNat (width n) 37)).bind
        (rouletteModGame keyLen encryptSym A n b) := by
  simp only [demKeyGame, demKeyGameOn, rouletteToDEMAdversary, rouletteReduction,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, ↓reduceIte, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind]
  rw [PMF.bind_comm]
  congr 1; funext x
  have hlen :
      (⟨(encUnary (x % 37)).length % 37, Nat.mod_lt _ (by decide)⟩ : Fin 37) =
        ⟨x % 37, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext
    simp only [encUnary_apply, List.length_replicate]
    exact Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))
  simp only [PMF.pure_bind, hlen, rouletteModGame, ProbComp.eval_bind, ProbComp.eval_pure]

private theorem eval_uniform_rouletteModGame (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (b : Bool) (n : ℕ) :
    ((PMF.uniformOfFintype (Fin 37)).bind
      fun r => rouletteModGame keyLen encryptSym A n b r.val) =
      ProbComp.eval (if b then
        idealRouletteExperiment (wordCipher encryptSym (fun _ _ _ => none) n)
          (BitString.sampleList (keyLen n)) (A n)
      else
        rouletteDEMExperiment keyLen encryptSym A n) := by
  simp only [rouletteModGame, Nat.mod_eq_of_lt (Fin.isLt _), Fin.eta]
  cases b <;>
    simp [rouletteDEMExperiment, rouletteExperiment, idealRouletteExperiment, wordCipher,
      ProbComp.eval_bind, ProbComp.eval_uniform, PMF.map, Function.comp_def]

private theorem advantage_demKeyGame_rouletteMod_le (width keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (b : Bool) (n : ℕ) :
    Game.advantage
        (ProbComp.eval
          (demKeyGame keyLen encryptSym (rouletteToDEMAdversary width A) b n))
        (ProbComp.eval (if b then
          idealRouletteExperiment (wordCipher encryptSym (fun _ _ _ => none) n)
            (BitString.sampleList (keyLen n)) (A n)
        else
          rouletteDEMExperiment keyLen encryptSym A n)) ≤
      (37 : ℝ≥0) / 2 ^ width n := by
  rw [eval_demKeyGame_rouletteToDEMAdversary, ← eval_uniform_rouletteModGame]
  exact Game.advantage_bind_sampleModNat_fin_le (width n) 37
    (rouletteModGame keyLen encryptSym A n b)

/-- Concrete DEM semantic-security reduction for Internet roulette: `rouletteDEMAdvantage` is
bounded by the distinguishing advantage of `rouletteToDEMAdversary width A` plus
`(74 : ℝ≥0) / 2 ^ width n` from approximating two `Fin 37` uniform wheel spins with
`ProbComp.sampleModNat (width n) 37`. -/
theorem rouletteDEMAdvantage_le_demKeyGame_add (width keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp RouletteBet) (n : ℕ) :
    rouletteDEMAdvantage keyLen encryptSym A n ≤
      Experiment.advantage
        (demKeyGame keyLen encryptSym (rouletteToDEMAdversary width A) false n)
        (demKeyGame keyLen encryptSym (rouletteToDEMAdversary width A) true n) +
        (74 : ℝ≥0) / 2 ^ width n := by
  let E : Cipher (List Bool) (Fin 37) (List Bool) := wordCipher encryptSym (fun _ _ _ => none) n
  let sampleKey := BitString.sampleList (keyLen n)
  have h0 := (Game.advantage_comm _ _).trans_le
    (advantage_demKeyGame_rouletteMod_le width keyLen encryptSym A false n)
  have h1 := (Game.advantage_comm _ _).trans_le
    (advantage_demKeyGame_rouletteMod_le width keyLen encryptSym A true n)
  change rouletteAdvantage E sampleKey (A n) ≤ _
  rw [rouletteAdvantage_eq_advantage_ideal]
  exact (Game.advantage_four_hop_le h0 h1).trans_eq (by ring)

/-- Asymptotic Theorem 2.9 ([BonehShoup2023], Section 2.2.4, p. 23): under
`DEMOneTimeKeyINDCPAOf encIndex keyLen encryptSym`, every uniform strict PPT adversary
`A : ℕ → List Bool → ProbComp RouletteBet` has negligible Internet roulette advantage. -/
theorem DEMOneTimeKeyINDCPAOf.negligible_rouletteDEMAdvantage
    {encIndex : Fin 37 ↪ List Bool} {encBet : RouletteBet ↪ List Bool}
    {keyLen : ℕ → ℕ} {encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool)}
    (hdem : DEMOneTimeKeyINDCPAOf encIndex keyLen encryptSym)
    {A : ℕ → List Bool → ProbComp RouletteBet} (hA : Probability.IsPPT encBet A) :
    Negligible (rouletteDEMAdvantage keyLen encryptSym A) := by
  have hadv :
      Negligible (fun n => Experiment.advantage
        (demKeyGame keyLen encryptSym (rouletteToDEMAdversary id A) false n)
        (demKeyGame keyLen encryptSym (rouletteToDEMAdversary id A) true n)) :=
    hdem (rouletteToDEMAdversary id A)
      (isPPT_rouletteToDEMAdversary ComputableInPolyTime.id' hA)
  exact negligible_of_le
    (hadv.add_fun (by simpa only [Nat.cast_ofNat, id_eq] using negligible_const_div_two_pow 74))
    (rouletteDEMAdvantage_le_demKeyGame_add id keyLen encryptSym A)

end Cslib.Crypto.Encryption
