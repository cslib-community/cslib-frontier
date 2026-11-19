/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Crypto.Computational.Encryption.PolyTime
public import CslibFrontier.Foundations.Data.BitString.ListParity
public import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Foundations.Data.BitString.DeltaMatroid.Basic
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Tactic.PPT

/-!
# Parity-prediction security from semantic security (Boneh–Shoup §2.2.3.2)

A semantically secure cipher over non-empty bit strings is secure against parity prediction
([BonehShoup2023], Section 2.2.3.2, Attack Game 2.3, Definition 2.4, and Theorem 2.8, pp. 20–22).
We formalize both the concrete exact advantage identity for a typed symmetric cipher
`Cipher K (BitString L) C` and the asymptotic theorem for a cipher with message space
`{0, 1}^{msgLen n}`, whose semantic security admits exactly the challenge pairs of two
`msgLen n`-bit messages, together with the uniform strict PPT certificate of the reduction.

Relative to [BonehShoup2023], §2.2.3.2, pp. 20–22, this formalization makes two hypotheses explicit:
* On a concrete `Cipher K (BitString L) C`,
  `parityAdvantage_eq_half_mul_advantage_parityReduction` requires `hL : 1 ≤ L` so messages have a
  last bit to flip via `flipLastBitString hL` (`m₀ ↦ m₀ ⊕ (0^{L-1} ‖ 1)`), and
  `hvalid : ∀ m₀ : BitString L, valid m₀ (flipLastBitString hL m₀) = true` so
  `Cipher.oneTimeExperiment` admits every pair submitted by
  `parityReduction (ProbComp.uniform (BitString L)) (flipLastBitString hL) (parity L) A`.
  (The book implicitly takes `L ≥ 1` and allows all fixed-length pairs in Attack Game 2.1.)
* On word messages `{0, 1}^{msgLen n}`, `parityWordAdvantage_eq_half_mul_demKeyGameOn` and
  `DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage` require `1 ≤ msgLen n`
  (`hpos : ∀ n, 1 ≤ msgLen n`) and `ComputableInPolyTime msgLen encUnary encUnary` for PPT
  message sampling. Checked counterexamples in `CslibFrontierTests.Crypto.ParityPrediction` show
  that `hL`, `hvalid`, and `hpos` are needed.

## Main definitions

* `Cslib.Crypto.Encryption.flipLastBitString`: flip the last bit of an `L`-bit string (`1 ≤ L`).
* `Cslib.Crypto.Encryption.parityExperiment`: parity-prediction attack game (Attack Game 2.3).
* `Cslib.Crypto.Encryption.parityAdvantage`: `Parityadv[A, E] := |Pr[W] - 1 / 2|`.
* `Cslib.Crypto.Encryption.parityReduction`: explicit semantic-security reduction `B` (Theorem 2.8).
* `Cslib.Crypto.Encryption.flipLastBitWord`: flip the last bit of a word of length `L`.
* `Cslib.Crypto.Encryption.parityWordExperiment`,
  `Cslib.Crypto.Encryption.parityWordAdvantage`,
  `Cslib.Crypto.Encryption.parityWordToDEMAdversary`: word-level experiment, advantage, and
  `WordAdversary` reduction running `parityReduction`.

## Main results

* `Cslib.Crypto.Encryption.parityAdvantage_eq_half_mul_advantage_parityReduction`: exact concrete
  identity `Parityadv[A, E] = (1 / 2) * SSadv[B, E]` (Theorem 2.8, p. 21).
* `Cslib.Crypto.Encryption.isPPT_parityWordToDEMAdversary`: uniform strict PPT certificate for
  `parityWordToDEMAdversary`.
* `Cslib.Crypto.Encryption.parityWordAdvantage_eq_half_mul_demKeyGameOn`: word-level exact
  identity at each `n` with `1 ≤ msgLen n`, the equation of the proof of Theorem 2.8.
* `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage`: asymptotic
  Theorem 2.8, from semantic security on challenge pairs of `msgLen n`-bit messages.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 2.2.3.2, Attack Game 2.3, Definition 2.4, Theorem 2.8, pp. 20–22.
-/

public section

namespace Cslib.Crypto.Encryption

open Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

section ParityPrediction

variable {K C : Type} {L : ℕ}

/-- Flip the last bit of an `L`-bit string (`m ↦ m ⊕ (0^{L-1} ‖ 1)`), requiring `1 ≤ L`. -/
def flipLastBitString {L : ℕ} (hL : 1 ≤ L) (m : BitString L) : BitString L :=
  BitString.flipOn {⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩} m

theorem flipLastBitString_involutive {L : ℕ} (hL : 1 ≤ L) :
    Function.Involutive (flipLastBitString hL) :=
  BitString.flipOn_involutive _

theorem parity_flipLastBitString {L : ℕ} (hL : 1 ≤ L) (m : BitString L) :
    parity L (flipLastBitString hL m) = !(parity L m) :=
  BitString.parityOn_univ_flipOn_singleton m ⟨L - 1, Nat.sub_lt hL Nat.one_pos⟩

/-- Parity-prediction attack game ([BonehShoup2023], Attack Game 2.3, p. 21). -/
@[expose] noncomputable def parityExperiment (E : Cipher K (BitString L) C)
    (sampleKey : ProbComp K) (A : C → ProbComp Bool) : Experiment := do
  let m ← ProbComp.uniform (BitString L)
  let k ← sampleKey
  let c ← E.encrypt k m
  let bHat ← A c
  return (bHat == parity L m)

/-- Parity-prediction advantage `Parityadv[A, E] := |Pr[W] - 1 / 2|`
([BonehShoup2023], Attack Game 2.3, p. 21). -/
@[expose] noncomputable def parityAdvantage (E : Cipher K (BitString L) C)
    (sampleKey : ProbComp K) (A : C → ProbComp Bool) : ℝ≥0 :=
  Game.guessingAdvantage (ProbComp.eval (parityExperiment E sampleKey A))

/-- Explicit semantic-security reduction `B` from a parity-prediction adversary `A`
([BonehShoup2023], Theorem 2.8, p. 21), parameterized by message sampler, bit-flip map, and
parity predicate so the typed and word-level theorems share one reduction program. -/
@[expose] noncomputable def parityReduction {M C : Type} (sampleMessage : ProbComp M)
    (flip : M → M) (par : M → Bool) (A : C → ProbComp Bool) :
    TwoStage Unit (MessagePair M) C Bool Bool where
  choose _ := do
    let m₀ ← sampleMessage
    return (⟨m₀, flip m₀⟩, par m₀)
  guess p₀ c := do
    let bHat ← A c
    return (bHat == p₀)

private theorem parityReduction_advantage_eq {K M C : Type} (E : Cipher K M C)
    (sampleKey : ProbComp K) (sampleMessage : ProbComp M) (flip : M → M)
    (par : M → Bool) {valid : M → M → Bool}
    (hvalid : ∀ m₀ ∈ (ProbComp.eval sampleMessage).support, valid m₀ (flip m₀) = true)
    (hflip_map : (ProbComp.eval sampleMessage).map flip = ProbComp.eval sampleMessage)
    (hpar_flip : ∀ m₀ ∈ (ProbComp.eval sampleMessage).support, par (flip m₀) = !(par m₀))
    (A : C → ProbComp Bool) :
    let exp : Experiment := do
      let m ← sampleMessage
      let k ← sampleKey
      let c ← E.encrypt k m
      let bHat ← A c
      return (bHat == par m)
    (Game.guessingAdvantage (ProbComp.eval exp) : ℝ) =
      (1 / 2 : ℝ) *
        (Experiment.advantage
          (E.oneTimeExperiment sampleKey valid (parityReduction sampleMessage flip par A) false)
          (E.oneTimeExperiment sampleKey valid
            (parityReduction sampleMessage flip par A) true) : ℝ) := by
  intro exp
  have heval0 :
      ProbComp.eval (E.oneTimeExperiment sampleKey valid
        (parityReduction sampleMessage flip par A) false) = ProbComp.eval exp := by
    simp only [Cipher.oneTimeExperiment, parityReduction, exp, lrExperiment,
      MessagePair.select_false, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
      PMF.pure_bind]
    rw [PMF.bind_comm]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun m₀ hm₀ => ?_
    simp [hvalid m₀ hm₀, ← PMF.bind_pure_comp, Function.comp_def]
  have heval1 :
      ProbComp.eval (E.oneTimeExperiment sampleKey valid
        (parityReduction sampleMessage flip par A) true) =
        (ProbComp.eval exp).map Bool.not := by
    have hnot_beq : ∀ x y : Bool, (x == !y) = !(x == y) := by decide
    let body : M → PMF Bool := fun m =>
      (ProbComp.eval sampleKey).bind fun k =>
        (ProbComp.eval (E.encrypt k m)).bind fun c =>
          (ProbComp.eval (A c)).bind fun bHat => PMF.pure (!(bHat == par m))
    have heq :
        ProbComp.eval (E.oneTimeExperiment sampleKey valid
          (parityReduction sampleMessage flip par A) true) =
          (ProbComp.eval sampleMessage).bind fun m₀ => body (flip m₀) := by
      simp only [Cipher.oneTimeExperiment, parityReduction, lrExperiment, MessagePair.select_true,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      rw [PMF.bind_comm]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun m₀ hm₀ => ?_
      have hp : par m₀ = !(par (flip m₀)) := by
        rw [hpar_flip m₀ hm₀, Bool.not_not]
      simp only [hvalid m₀ hm₀, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, hp, hnot_beq,
        body]
    have hmap :
        (ProbComp.eval sampleMessage).bind (fun m₀ => body (flip m₀)) =
          (ProbComp.eval sampleMessage).bind body := by
      nth_rw 2 [← hflip_map]
      rw [PMF.bind_map]
      rfl
    rw [heq, hmap]
    simp only [exp, body, ProbComp.eval_bind, ProbComp.eval_pure, ← PMF.bind_pure_comp,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  rw [Game.coe_guessingAdvantage, Experiment.advantage, heval0, heval1, Game.coe_advantage,
    Game.succProbability_not, Game.failProbability_eq,
    NNReal.coe_sub (Game.succProbability_le_one _), NNReal.coe_one]
  have key : ∀ p : ℝ, |p - (1 - p)| = 2 * |p - 1 / 2| := fun p => by
    rw [show p - (1 - p) = 2 * (p - 1 / 2) by ring, abs_mul, abs_of_pos (by norm_num)]
  rw [key, abs_sub_comm]
  ring

/-- **Concrete advantage relation for Theorem 2.8** ([BonehShoup2023], p. 21):
`Parityadv[A, E] = (1 / 2) * SSadv[B, E]` with
`B := parityReduction (ProbComp.uniform (BitString L)) (flipLastBitString hL) (parity L) A`. -/
theorem parityAdvantage_eq_half_mul_advantage_parityReduction (E : Cipher K (BitString L) C)
    (sampleKey : ProbComp K) (hL : 1 ≤ L) {valid : BitString L → BitString L → Bool}
    (hvalid : ∀ m₀ : BitString L, valid m₀ (flipLastBitString hL m₀) = true)
    (A : C → ProbComp Bool) :
    (parityAdvantage E sampleKey A : ℝ) =
      (1 / 2 : ℝ) *
        (Experiment.advantage
          (E.oneTimeExperiment sampleKey valid
            (parityReduction (ProbComp.uniform (BitString L))
              (flipLastBitString hL) (parity L) A) false)
          (E.oneTimeExperiment sampleKey valid
            (parityReduction (ProbComp.uniform (BitString L))
              (flipLastBitString hL) (parity L) A) true) : ℝ) := by
  have hflip_map :
      (ProbComp.eval (ProbComp.uniform (BitString L))).map (flipLastBitString hL) =
        ProbComp.eval (ProbComp.uniform (BitString L)) := by
    rw [ProbComp.eval_uniform, ← PMF.bind_pure_comp]
    simpa [Function.comp_def] using Probability.PMF.uniformOfFintype_bind_bijective
      (flipLastBitString_involutive hL).bijective (k := PMF.pure) (fun _ => rfl)
  exact parityReduction_advantage_eq E sampleKey (ProbComp.uniform (BitString L))
    (flipLastBitString hL) (parity L)
    (fun m₀ _ => hvalid m₀) hflip_map (fun m₀ _ => parity_flipLastBitString hL m₀) A

end ParityPrediction

section ParityPredictionWord

/-- Flip the last bit of a word of length `L` via XOR with `0^{L-1} ‖ 1`
([BonehShoup2023], p. 21: `m₀ ⊕ (0^{L-1} ‖ 1)`). -/
def flipLastBitWord (L : ℕ) (w : List Bool) : List Bool :=
  BitString.listXor L [w, List.replicate (L - 1) false ++ [true]]

theorem length_flipLastBitWord (L : ℕ) (w : List Bool) : (flipLastBitWord L w).length = L :=
  BitString.length_listXor L _

private theorem wordParity_lastUnitVec (L : ℕ) :
    BitString.wordParity (List.replicate (L - 1) false ++ [true]) = true := by
  have h : ∀ k : ℕ, BitString.wordParity (List.replicate k false ++ [true]) = true := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ] using ih
  exact h (L - 1)

private theorem parity_ofList_lastUnitVec {L : ℕ} (hL : 1 ≤ L) :
    parity L (BitString.ofList L (List.replicate (L - 1) false ++ [true])) = true := by
  rw [parity, ← BitString.wordParity_ofFn]
  have heq : List.ofFn (BitString.ofList L (List.replicate (L - 1) false ++ [true])) =
      List.replicate (L - 1) false ++ [true] :=
    BitString.ofFn_ofList (by simp; omega)
  rw [heq, wordParity_lastUnitVec L]

theorem wordParity_flipLastBitWord {L : ℕ} (hL : 1 ≤ L) {w : List Bool} (hw : w.length = L) :
    BitString.wordParity (flipLastBitWord L w) = !(BitString.wordParity w) := by
  have hw_of : w = List.ofFn (BitString.ofList L w) := (BitString.ofFn_ofList hw).symm
  rw [flipLastBitWord, BitString.listXor_pair, BitString.wordParity_ofFn,
    parityOn_add, ← parity, parity_ofList_lastUnitVec hL]
  nth_rw 2 [hw_of]
  rw [BitString.wordParity_ofFn, ← parity]
  cases parity L (BitString.ofList L w) <;> rfl

/-- Word-level parity-prediction experiment over `{0, 1}^{msgLen n}`. -/
@[expose] noncomputable def parityWordExperiment (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp Bool) (n : ℕ) : Experiment := do
  let m ← BitString.sampleList (msgLen n)
  let k ← BitString.sampleList (keyLen n)
  let c ← encryptSym n k m
  let bHat ← A n c
  return (bHat == BitString.wordParity m)

/-- Word-level parity-prediction advantage `Parityadv[A, E](n) = |Pr[W] - 1 / 2|`. -/
@[expose] noncomputable def parityWordAdvantage (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp Bool) (n : ℕ) : ℝ≥0 :=
  Game.guessingAdvantage (ProbComp.eval (parityWordExperiment msgLen keyLen encryptSym A n))

/-- Explicit `WordAdversary` reduction for parity prediction on `{0, 1}^{msgLen n}`, running
`parityReduction`. -/
@[expose] noncomputable def parityWordToDEMAdversary (msgLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp Bool) : WordAdversary where
  choose n _ := do
    let choice ← (parityReduction (BitString.sampleList (msgLen n))
      (flipLastBitWord (msgLen n)) BitString.wordParity (A n)).choose ()
    return ((choice.1.msg₀, choice.1.msg₁), [choice.2])
  guess n st ct :=
    (parityReduction (BitString.sampleList (msgLen n))
      (flipLastBitWord (msgLen n)) BitString.wordParity (A n)).guess
      (BitString.wordParity st) ct

private theorem computableInPolyTime_wordParity {α : Type} {enc : α ↪ List Bool}
    {f : α → List Bool} (hf : ComputableInPolyTime f enc encBits) :
    ComputableInPolyTime (fun x => BitString.wordParity (f x)) enc encBool := by
  simpa only [BitString.wordParity, List.foldr_eq_foldl] using
    ComputableInPolyTime.bitsFoldlWithInput Bool.xor hf (.const false)

private theorem computableInPolyTime_flipLastBitWord {α : Type} {enc : α ↪ List Bool}
    {L : α → ℕ} {w : α → List Bool}
    (hL : ComputableInPolyTime L enc encUnary)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => flipLastBitWord (L a) (w a)) enc encBits := by
  fun_prop [flipLastBitWord]

attribute [local fun_prop] computableInPolyTime_wordParity computableInPolyTime_flipLastBitWord

/-- Uniform strict PPT certificate for `parityWordToDEMAdversary`. -/
theorem isPPT_parityWordToDEMAdversary {msgLen : ℕ → ℕ}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    {A : ℕ → List Bool → ProbComp Bool}
    (hA : IsPPTOn (encPair encUnary encBits) encBool (fun ⟨n, ct⟩ => A n ct)) :
    AdversaryOf.IsPPT encBits (parityWordToDEMAdversary msgLen A) := by
  refine ⟨?_, ?_⟩
  · dsimp only [parityWordToDEMAdversary, parityReduction]
    ppt
  · dsimp only [parityWordToDEMAdversary, parityReduction]
    ppt

/-- Exact word-level advantage identity of the proof of Theorem 2.8 ([BonehShoup2023], p. 21) at
each `n` with `1 ≤ msgLen n`: `Parityadv[A, E](n) = (1 / 2) · SSadv[B, E](n)` for
`B := parityWordToDEMAdversary msgLen A`, in Attack Game 2.1 with challenge pairs of two
`msgLen n`-bit messages. Derived from `parityReduction_advantage_eq`. -/
theorem parityWordAdvantage_eq_half_mul_demKeyGameOn (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp Bool) {n : ℕ} (hn : 1 ≤ msgLen n) :
    (parityWordAdvantage msgLen keyLen encryptSym A n : ℝ) =
      (1 / 2 : ℝ) *
        (Game.advantage
          (ProbComp.eval (demKeyGameOn
            (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
            keyLen encryptSym (parityWordToDEMAdversary msgLen A) false n))
          (ProbComp.eval (demKeyGameOn
            (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
            keyLen encryptSym (parityWordToDEMAdversary msgLen A) true n)) : ℝ) := by
  let E_word : Cipher (List Bool) (List Bool) (List Bool) :=
    ⟨fun k m => encryptSym n k m, fun _ _ => pure []⟩
  let valid : List Bool → List Bool → Bool := fun m₀ m₁ =>
    m₀.length == msgLen n && m₁.length == msgLen n
  have hgame : ∀ b : Bool,
      ProbComp.eval (demKeyGameOn
        (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n)
        keyLen encryptSym (parityWordToDEMAdversary msgLen A) b n) =
        ProbComp.eval (E_word.oneTimeExperiment (BitString.sampleList (keyLen n)) valid
          (parityReduction (BitString.sampleList (msgLen n))
            (flipLastBitWord (msgLen n)) BitString.wordParity (A n)) b) := by
    intro b
    cases b <;>
      simp only [demKeyGameOn, E_word, valid, Cipher.oneTimeExperiment, lrExperiment,
        parityWordToDEMAdversary, parityReduction, ChoiceOut.msg₀, ChoiceOut.msg₁,
        MessagePair.select_false, MessagePair.select_true, Bool.false_eq_true, ↓reduceIte,
        ProbComp.eval_bind, ProbComp.eval_pure, BitString.wordParity_cons, BitString.wordParity_nil,
        Bool.xor_false, PMF.bind_bind, PMF.pure_bind]
  rw [parityWordAdvantage, Game.advantage, hgame false, hgame true]
  exact parityReduction_advantage_eq E_word (BitString.sampleList (keyLen n))
    (BitString.sampleList (msgLen n)) (flipLastBitWord (msgLen n)) BitString.wordParity
    (fun m₀ hm₀ => by
      rw [BitString.eval_sampleList] at hm₀
      simp [valid, BitString.length_of_mem_support_uniformList hm₀, length_flipLastBitWord])
    (by
      rw [BitString.eval_sampleList]
      exact BitString.uniformList_map_listXor (msgLen n) _)
    (fun m₀ hm₀ => by
      rw [BitString.eval_sampleList] at hm₀
      exact wordParity_flipLastBitWord hn (BitString.length_of_mem_support_uniformList hm₀))
    (A n)

/-- **Theorem 2.8** ([BonehShoup2023], Section 2.2.3.2, p. 21): a semantically secure cipher with
message space `{0, 1}^L` is secure against parity prediction. Here `L = msgLen n` at security
parameter `n`, with `1 ≤ msgLen n` (the book leaves `1 ≤ L` implicit: at `L = 0` the parity is
constant and the conclusion fails) and `msgLen` computable in polynomial time in unary. The
premise is semantic security in Attack Game 2.1 (Definition 2.2, p. 16) with a uniform
`keyLen n`-bit key, against uniform strict PPT two-stage adversaries, for exactly the challenge
pairs of the message space: two `msgLen n`-bit messages. The conclusion: every uniform strict PPT
predictor `A`, given `1ⁿ` and the ciphertext of a uniform `msgLen n`-bit message, has negligible
advantage `|Pr[W] - 1 / 2|` in Attack Game 2.3 (`parityWordAdvantage`). The reduction
`parityWordToDEMAdversary` is certified by `isPPT_parityWordToDEMAdversary`, and
`parityWordAdvantage_eq_half_mul_demKeyGameOn` is the proof's exact equation. -/
theorem DEMOneTimeKeyINDCPAOn.negligible_parityWordAdvantage {msgLen keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hsec : DEMOneTimeKeyINDCPAOn
      (fun n _ m₀ m₁ => m₀.length == msgLen n && m₁.length == msgLen n) encBits keyLen encryptSym)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hpos : ∀ n, 1 ≤ msgLen n)
    {A : ℕ → List Bool → ProbComp Bool}
    (hA : IsPPTOn (encPair encUnary encBits) encBool (fun ⟨n, ct⟩ => A n ct)) :
    Negligible (parityWordAdvantage msgLen keyLen encryptSym A) := by
  refine ((hsec _ (isPPT_parityWordToDEMAdversary hmsgLen hA)).const_mul (1 / 2 : ℝ≥0)).congr
    fun n => ?_
  apply NNReal.coe_injective
  simpa [NNReal.coe_mul] using
    (parityWordAdvantage_eq_half_mul_demKeyGameOn msgLen keyLen encryptSym A (hpos n)).symm

end ParityPredictionWord

end Cslib.Crypto.Encryption
