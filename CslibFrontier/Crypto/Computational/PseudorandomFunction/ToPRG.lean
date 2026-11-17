/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Primitives.PRF.ToPRG
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Traverse
import CslibFrontier.Foundations.Control.Monad.MapM
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Probability.BitString.List

/-!
# Pseudorandom generator from a word-level pseudorandom function

Evaluating a word-level keyed family `family` at `ℓ n` distinct `inLen n`-bit points
`x n : Fin (ℓ n) ↪ BitString (inLen n)` and concatenating the resulting `outLen n`-bit outputs
gives `prgFromPRF family ℓ inLen x` of length `ℓ n * outLen n` ([BonehShoup2023], §4.4.4,
Theorem 4.8, p. 138).

The word reduction `prgFromPRFReduction ℓ inLen outLen x A` wraps `PRF.prgReduction`, so
certifying it via `isOraclePPT_prgFromPRFReduction` also certifies `PRF.prgReduction`. Theorem
`PseudorandomFunctionOver.toPRG` uses `PseudorandomFunctionOver` rather than the fixed-width
`PseudorandomFunction` (`inLen = outLen = id`), which cannot expand at seed length `0`.

## Main definitions

* `Cslib.Crypto.prgFromPRF`: word generator obtained by evaluating `family` at `x`.
* `Cslib.Crypto.prgFromPRFReduction`: word PRF distinguisher wrapping `PRF.prgReduction`.

## Main results

* `Cslib.Crypto.computableInPolyTime_prgFromPRF`: `prgFromPRF` is deterministic polynomial time.
* `Cslib.Crypto.isOraclePPT_prgFromPRFReduction`: `prgFromPRFReduction` is uniform strict
  oracle PPT.
* `Cslib.Crypto.advantage_prgFromPRF_eq`: PRG advantage of `A` equals PRF advantage of
  `prgFromPRFReduction`.
* `Cslib.Crypto.indistinguishable_prgFromPRF`: computational indistinguishability without
  strict expansion.
* `Cslib.Crypto.PseudorandomFunctionOver.toPRG`: Boneh–Shoup Theorem 4.8 as a
  `PseudorandomGenerator`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §4.4.4 (Theorem 4.8, p. 138).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

section Construction

/-- Evaluate `family` on a `seed` at the `ℓ seed.length` distinct `inLen seed.length`-bit domain
points `x seed.length 0, ..., x seed.length (ℓ seed.length - 1)` and concatenate the replies
([BonehShoup2023], §4.4.4, p. 138). -/
@[expose] def prgFromPRF (family : List Bool → List Bool → List Bool)
    (ℓ inLen : ℕ → ℕ) (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (seed : List Bool) :
    List Bool :=
  ((List.ofFn fun i : Fin (ℓ seed.length) => List.ofFn (x seed.length i)).map
    (family seed)).flatten

/-- On a seed of length `n`, `prgFromPRF` outputs `ℓ n * outLen n` bits whenever `family`
produces `outLen n`-bit replies on valid `inLen n`-bit queries. -/
theorem length_prgFromPRF {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hlength : ∀ key query, query.length = inLen key.length →
      (family key query).length = outLen key.length)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (seed : List Bool) :
    (prgFromPRF family ℓ inLen x seed).length = ℓ seed.length * outLen seed.length := by
  simp only [prgFromPRF, List.length_flatten, Function.comp_def, List.map_ofFn, List.sum_ofFn]
  have hterm (i : Fin (ℓ seed.length)) :
      (family seed (List.ofFn (x seed.length i))).length = outLen seed.length :=
    hlength seed _ (List.length_ofFn)
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `prgFromPRF` is deterministic polynomial time when `family` and the point list are. -/
theorem computableInPolyTime_prgFromPRF
    {family : List Bool → List Bool → List Bool} {ℓ inLen : ℕ → ℕ}
    {x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)}
    (hfamily : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hx : ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) encUnary (encList encBits)) :
    ComputableInPolyTime (prgFromPRF family ℓ inLen x) encBits encBits := by
  have hpts : ComputableInPolyTime
      (fun seed : List Bool => List.ofFn fun i : Fin (ℓ seed.length) => List.ofFn (x seed.length i))
      encBits (encList encBits) := hx.comp ComputableInPolyTime.length_bits
  have hmapped : ComputableTidilyInPolyTime
      (fun seed : List Bool =>
        (List.ofFn fun i : Fin (ℓ seed.length) => List.ofFn (x seed.length i)).map
          (family seed))
      encBits (encList encBits) :=
    ComputableTidilyInPolyTime.mapWithInput hpts.tidy hfamily.tidy
  exact .of_tidy (ComputableTidilyInPolyTime.bitsFlatten hmapped)

end Construction

section Reduction

/-- Word-level PRF reduction wrapping the finite reduction `PRF.prgReduction`: queries the word
oracle at `x n 0, ..., x n (ℓ n - 1)`, truncating/padding each reply to `outLen n` bits via
`BitString.ofList (outLen n)`, concatenates the replies, and passes them to `A n`. -/
@[expose] def prgFromPRFReduction (ℓ inLen outLen : ℕ → ℕ)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) : OracleDistinguisher :=
  fun n _ =>
    ProbOracleComp.simulate
      (fun q : BitString (inLen n) =>
        BitString.ofList (outLen n) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), List.ofFn q))
      (PRF.prgReduction (x n) fun y =>
        A n (List.ofFn fun i => List.ofFn (y i)).flatten)

/-- `prgFromPRFReduction` as a word program: the points are sent to the oracle in one list
traversal, each reply is cut to `outLen n` bits, padded back to `outLen n` bits, and the
concatenation is given to `A n`. -/
private def prgFromPRFReductionWord (ℓ inLen outLen : ℕ → ℕ)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) : OracleDistinguisher :=
  fun n _ => do
    let replies ← (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)).mapM fun q =>
      List.take (outLen n) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), q)
    ProbOracleComp.sample (A n (replies.flatMap fun r =>
      (r ++ List.replicate (outLen n) false).take (outLen n)))

private theorem prgFromPRFReductionWord_eq (ℓ inLen outLen : ℕ → ℕ)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) :
    prgFromPRFReductionWord ℓ inLen outLen x A = prgFromPRFReduction ℓ inLen outLen x A := by
  funext n input
  have hflat (y : Fin (ℓ n) → BitString (outLen n)) :
      (List.ofFn fun i => List.ofFn (y i)).flatten = (List.ofFn y).flatMap List.ofFn := by
    rw [List.flatMap, List.map_ofFn, Function.comp_def]
  have hreplies : ((List.finRange (ℓ n)).mapM fun i => BitString.ofList (outLen n) <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), List.ofFn (x n i))) =
      List.map (BitString.ofList (outLen n)) <$> (List.finRange (ℓ n)).mapM fun i =>
        List.take (outLen n) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), List.ofFn (x n i)) := by
    rw [List.map_mapM]
    congr 1
    funext i
    rw [Functor.map_map]
    exact congrArg (· <$> _) (funext fun r => (BitString.ofList_take _ r).symm)
  simp only [prgFromPRFReductionWord, prgFromPRFReduction, PRF.prgReduction, PRF.queryPoints,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pi, ProbOracleComp.simulate_query,
    ProbOracleComp.simulate_sample, hflat]
  rw [← bind_map_left List.ofFn _ fun ys => ProbOracleComp.sample (A n (ys.flatMap List.ofFn)),
    OracleComp.map_ofFn_pi, hreplies, bind_map_left, List.ofFn_eq_map, List.mapM_map]
  simp only [List.flatMap_map, BitString.ofFn_ofList_eq_take, Function.comp_def]

/-- **Efficiency of the word PRF-to-PRG reduction.** For every uniform strict PPT distinguisher `A`,
`prgFromPRFReduction` is uniform strict oracle PPT whenever the query list and output widths are
deterministic polynomial time. -/
theorem isOraclePPT_prgFromPRFReduction {ℓ inLen outLen : ℕ → ℕ}
    {x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)} {A : Distinguisher}
    (hx : ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) encUnary (encList encBits))
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hA : IsPPT encBool A) :
    IsOraclePPT encBool (prgFromPRFReduction ℓ inLen outLen x A) := by
  rw [← prgFromPRFReductionWord_eq]
  have hreplies := IsOraclePPTOn.mapM_query_take () hx hout
  have hw := hout.comp (ComputableInPolyTime.fst encUnary (encList encBits))
  have hw' := hw.comp (ComputableInPolyTime.fst (encPair encUnary (encList encBits)) encBits)
  have hpad : ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => p.2.flatMap fun r =>
        (r ++ List.replicate (outLen p.1) false).take (outLen p.1))
      (encPair encUnary (encList encBits)) encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.snd _ _)
      (((ComputableInPolyTime.snd _ _).bitsAppend
        ((ComputableInPolyTime.bitsReplicate false).comp hw')).bitsTakeWithInput hw')
  have hsample : IsOraclePPTOn (Operation := Unit) (encPair encUnary (encList encBits)) encBool
      (fun p : ℕ × List (List Bool) => ProbOracleComp.sample (A p.1 (p.2.flatMap fun r =>
        (r ++ List.replicate (outLen p.1) false).take (outLen p.1)))) :=
    hA.on.isOraclePPTOn.preprocess' ((ComputableInPolyTime.fst _ _).prod hpad)
  unfold prgFromPRFReductionWord
  have hbody := hreplies.bind_with hsample (second := fun n replies => ProbOracleComp.sample
    (A n (replies.flatMap fun r => (r ++ List.replicate (outLen n) false).take (outLen n))))
  exact (hbody.preprocess' (ComputableInPolyTime.fst encUnary encBits)).isOraclePPT

end Reduction

section Security

/-- Against a keyed family whose answers to `inLen n`-bit queries under `n`-bit keys have
`outLen n` bits, the word PRG real experiment equals the word PRF real experiment of
`prgFromPRFReduction`. -/
theorem eval_prgRealGame_prgFromPRF
    {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hlength : ∀ key query, query.length = inLen key.length →
      (family key query).length = outLen key.length)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgRealGame (prgFromPRF family ℓ inLen x) A n) =
      ProbComp.eval (prfRealGame inLen family (prgFromPRFReduction ℓ inLen outLen x A) n) := by
  simp only [prgRealGame, prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.ext fun b => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun key => ?_
  by_cases hmem : key ∈ (BitString.uniformList n).support
  · have hkeyLen : key.length = n := BitString.length_of_mem_support_uniformList hmem
    have hquery (q : BitString (inLen n)) :
        (BitString.ofList (outLen n) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), List.ofFn q)).run
          (fun request => pure (prfOracle family (inLen n) key request.2)) =
        pure (BitString.ofList (outLen n) (family key (List.ofFn q))) := by
      simp only [ProbOracleComp.run_map, ProbOracleComp.run_query, map_pure, prfOracle,
        List.length_ofFn, ite_true]
    have hconcat :
        (List.ofFn fun i : Fin (ℓ n) =>
          List.ofFn (BitString.ofList (outLen n) (family key (List.ofFn (x n i))))).flatten =
        prgFromPRF family ℓ inLen x key := by
      rw [prgFromPRF]
      congr 1
      rw [hkeyLen, List.map_ofFn]
      congr 1
      funext i
      exact BitString.ofFn_ofList
        ((hlength key _ (by rw [List.length_ofFn, hkeyLen])).trans (congrArg outLen hkeyLen))
    have hbody :
        ProbComp.eval (A n (prgFromPRF family ℓ inLen x key)) =
          ProbComp.eval ((prgFromPRFReduction ℓ inLen outLen x A n []).run
            fun request => pure (prfOracle family (inLen n) key request.2)) := by
      simp only [prgFromPRFReduction, PRF.prgReduction, ProbOracleComp.run_simulate,
        ProbOracleComp.run_bind, hquery, PRF.run_queryPoints, pure_bind, ProbOracleComp.run_sample,
        hconcat]
    rw [hbody]
  · simp only [PMF.mem_support_iff, ne_eq, not_not] at hmem
    simp [hmem]

/-- The uniform-word PRG ideal experiment equals the word PRF ideal experiment of
`prgFromPRFReduction`. -/
theorem eval_prgIdealGame_prgFromPRFReduction
    (ℓ inLen outLen : ℕ → ℕ) (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n))
    (A : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgIdealGame (fun n => ℓ n * outLen n) A n) =
      ProbComp.eval (prfIdealGame inLen outLen (prgFromPRFReduction ℓ inLen outLen x A) n) := by
  have hprf :
      prfIdealGame inLen outLen (prgFromPRFReduction ℓ inLen outLen x A) n =
        PRF.idealExperiment (PRF.prgReduction (x n)
          fun y : Fin (ℓ n) → BitString (outLen n) =>
            A n (List.ofFn fun i => List.ofFn (y i)).flatten) := by
    simp only [prfIdealGame, PRF.idealExperiment, prgFromPRFReduction, ProbOracleComp.run_simulate]
    congr 1
    funext table
    congr 1
    funext q
    simp only [ProbOracleComp.run_map, ProbOracleComp.run_query, map_pure, randomFunctionOracle,
      List.length_ofFn, ite_true, BitString.ofList_ofFn]
  rw [hprf, PRF.eval_idealExperiment_prgReduction, PRG.Generator.idealExperiment,
    eval_prgIdealGame, distinguishingGame_eq_bind]
  have hmap :
      (PMF.uniformOfFintype (Fin (ℓ n) → BitString (outLen n))).map
          (fun y => (List.ofFn fun i => List.ofFn (y i)).flatten) =
        BitString.uniformList (ℓ n * outLen n) := by
    simpa only [List.take_of_length_le (List.length_ofFn.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      BitString.uniformOfFintype_map_flatten_take (m := ℓ n) (w := outLen n)
        (fun _ => outLen n) (fun _ => le_rfl)
  change (BitString.uniformList (ℓ n * outLen n)).bind (fun word => ProbComp.eval (A n word)) = _
  rw [← hmap, PMF.bind_map]
  rfl

/-- **Concrete word-level advantage identity** ([BonehShoup2023], Theorem 4.8, p. 138): for any
keyed family whose answers to `inLen n`-bit queries under `n`-bit keys have `outLen n` bits and any
word distinguisher `A`, the PRG distinguishing advantage against `prgFromPRF family ℓ inLen x`
equals the PRF distinguishing advantage of `prgFromPRFReduction ℓ inLen outLen x A`. -/
theorem advantage_prgFromPRF_eq
    {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hlength : ∀ key query, query.length = inLen key.length →
      (family key query).length = outLen key.length)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (prgRealGame (prgFromPRF family ℓ inLen x) A n))
        (ProbComp.eval (prgIdealGame (fun n => ℓ n * outLen n) A n)) =
      Game.advantage
        (ProbComp.eval (prfRealGame inLen family (prgFromPRFReduction ℓ inLen outLen x A) n))
        (ProbComp.eval (prfIdealGame inLen outLen (prgFromPRFReduction ℓ inLen outLen x A) n)) := by
  rw [eval_prgRealGame_prgFromPRF hlength x A n,
    eval_prgIdealGame_prgFromPRFReduction ℓ inLen outLen x A n]

/-- The generated distribution `prgFromPRF` is computationally indistinguishable from uniform words
of length `ℓ n * outLen n` whenever `family` is a `PseudorandomFunctionOver inLen outLen` and
both the distinct query list and output width are deterministic polynomial time. -/
theorem indistinguishable_prgFromPRF
    {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hfamily : PseudorandomFunctionOver inLen outLen family)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n))
    (hx : ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) encUnary (encList encBits))
    (hout : ComputableInPolyTime outLen encUnary encUnary) :
    ComputationallyIndistinguishable (generatorEnsemble (prgFromPRF family ℓ inLen x))
      (fun n => BitString.uniformList (ℓ n * outLen n)) := by
  intro A hA
  have heq : (fun n => Game.advantage
      (distinguishingGame (generatorEnsemble (prgFromPRF family ℓ inLen x) n) (A n))
      (distinguishingGame (BitString.uniformList (ℓ n * outLen n)) (A n))) =
      fun n => Game.advantage
        (ProbComp.eval (prfRealGame inLen family (prgFromPRFReduction ℓ inLen outLen x A) n))
        (ProbComp.eval (prfIdealGame inLen outLen (prgFromPRFReduction ℓ inLen outLen x A) n)) := by
    funext n
    simpa only [eval_prgRealGame, eval_prgIdealGame] using
      advantage_prgFromPRF_eq hfamily.length_eq x A n
  rw [heq]
  exact hfamily.secure _ (isOraclePPT_prgFromPRFReduction hx hout hA)

private theorem computableInPolyTime_outLen_of_pos
    {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hfamily : PseudorandomFunctionOver inLen outLen family)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n))
    (hx : ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) encUnary (encList encBits))
    (hpos : ∀ n, 0 < ℓ n) :
    ComputableInPolyTime outLen encUnary encUnary := by
  have heq (n : ℕ) :
      outLen n = (family (List.replicate n false)
        ((List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)).headD [])).length := by
    let q := (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)).headD []
    have hmem : q ∈ List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i) := by
      have hn := hpos n
      dsimp only [q]
      cases hlist : (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) with
      | nil =>
        have hlen := congrArg List.length hlist
        simp only [List.length_ofFn, List.length_nil] at hlen
        omega
      | cons => simp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
    have hqLen : q.length = inLen n := by rw [← hi, List.length_ofFn]
    simpa only [List.length_replicate] using (hfamily.length_eq (List.replicate n false) q
      (by simpa only [List.length_replicate] using hqLen)).symm
  have hpoly : ComputableInPolyTime
      (fun n => (family (List.replicate n false)
        ((List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)).headD [])).length)
      encUnary encUnary :=
    ComputableInPolyTime.length_bits_comp (hfamily.polyTime.comp
      ((ComputableInPolyTime.bitsReplicate false).prod ((ComputableInPolyTime.headD []).comp hx)))
  simpa only [← heq] using hpoly

/-- **Pseudorandom generator from a pseudorandom function** ([BonehShoup2023], §4.4.4,
Theorem 4.8, p. 138): evaluating a `PseudorandomFunctionOver inLen outLen` at `ℓ n` efficiently
computable distinct `inLen n`-bit inputs yields a `PseudorandomGenerator` of output length
`ℓ n * outLen n`, whenever `∀ n, n < ℓ n * outLen n`. -/
theorem PseudorandomFunctionOver.toPRG
    {family : List Bool → List Bool → List Bool} {ℓ inLen outLen : ℕ → ℕ}
    (hfamily : PseudorandomFunctionOver inLen outLen family)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n))
    (hx : ComputableInPolyTime
      (fun n => List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i)) encUnary (encList encBits))
    (hstretch : ∀ n, n < ℓ n * outLen n) :
    PseudorandomGenerator (prgFromPRF family ℓ inLen x) (fun n => ℓ n * outLen n) :=
  PseudorandomGenerator.of_indistinguishable
    (computableInPolyTime_prgFromPRF hfamily.polyTime hx)
    (length_prgFromPRF hfamily.length_eq x)
    hstretch
    (indistinguishable_prgFromPRF hfamily x hx
      (computableInPolyTime_outLen_of_pos hfamily x hx fun n =>
        Nat.pos_of_ne_zero fun h0 => by simpa [h0] using hstretch n))

end Security

end Cslib.Crypto
