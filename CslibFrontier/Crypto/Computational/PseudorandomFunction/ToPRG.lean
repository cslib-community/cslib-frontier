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
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Tactic.EncLen

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

private def prgQueryStep (outLen : ℕ → ℕ) (n : ℕ) (state : List (List Bool) × List Bool) :
    WordOracleComp Unit (List (List Bool) × List Bool) :=
  if state.1.isEmpty then pure state
  else do
    let reply ← List.take (outLen n) <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), state.1.headD [])
    return (state.1.tail, state.2 ++ (reply ++ List.replicate (outLen n) false).take (outLen n))

private def prgFromPRFReductionLoop (ℓ inLen outLen : ℕ → ℕ)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) : OracleDistinguisher :=
  fun n _ => do
    let bits ← Prod.snd <$>
      OracleComp.iterate (ℓ n) (prgQueryStep outLen n)
        (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), [])
    ProbOracleComp.sample (A n bits)

private theorem iterate_prgQueryStep {k a w : ℕ} (f : Fin k → BitString a) (acc : List Bool) :
    (Prod.snd <$> OracleComp.iterate k (prgQueryStep (fun _ => w) 0)
      (List.ofFn (fun i => List.ofFn (f i)), acc)) =
      ((fun y : Fin k → BitString w =>
        acc ++ (List.ofFn fun i => List.ofFn (y i)).flatten) <$>
        OracleComp.pi fun i : Fin k =>
          BitString.ofList w <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), List.ofFn (f i))) := by
  induction k generalizing acc with
  | zero =>
    change (Prod.snd <$> pure ([], acc)) =
      ((fun _ => acc ++ [].flatten) <$> pure Fin.elim0)
    simp
  | succ k ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.pi_succ, List.ofFn_succ, map_bind]
    have hstep : prgQueryStep (fun _ => w) 0
        (List.ofFn (f 0) :: List.ofFn (fun j => List.ofFn (f j.succ)), acc) =
        ((fun y0 : BitString w =>
          (List.ofFn (fun j : Fin k => List.ofFn (f j.succ)), acc ++ List.ofFn y0)) <$>
          (BitString.ofList w <$>
            ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
              ((), List.ofFn (f 0)))) := by
      simp only [prgQueryStep, List.isEmpty_cons, Bool.false_eq_true, ite_false,
        List.headD_cons, List.tail_cons, Functor.map_map, bind_pure_comp]
      congr 1
      funext reply
      rw [← BitString.ofFn_ofList_eq_take, BitString.ofList_take]
    rw [hstep, bind_map_left, map_bind]
    congr 1
    funext y0
    have hrec : (Prod.snd <$> OracleComp.iterate k (prgQueryStep (fun _ => w) 0)
        (List.ofFn (fun j => List.ofFn (f j.succ)), acc ++ List.ofFn y0)) =
        ((fun rest : Fin k → BitString w =>
          acc ++ List.ofFn y0 ++ (List.ofFn fun j => List.ofFn (rest j)).flatten) <$>
          OracleComp.pi fun j : Fin k =>
            BitString.ofList w <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), List.ofFn (f j.succ))) :=
      ih (fun j => f j.succ) (acc ++ List.ofFn y0)
    rw [Functor.map_map]
    simpa only [Functor.map_map, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.flatten_cons,
      List.append_assoc] using hrec

private theorem prgFromPRFReductionLoop_eq (ℓ inLen outLen : ℕ → ℕ)
    (x : ∀ n, Fin (ℓ n) ↪ BitString (inLen n)) (A : Distinguisher) (n : ℕ) (input : List Bool) :
    prgFromPRFReductionLoop ℓ inLen outLen x A n input =
      prgFromPRFReduction ℓ inLen outLen x A n input := by
  simp only [prgFromPRFReductionLoop, prgFromPRFReduction, PRF.prgReduction, PRF.queryPoints,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_pi, ProbOracleComp.simulate_query,
    ProbOracleComp.simulate_sample]
  have hstep : prgQueryStep outLen n = prgQueryStep (fun _ => outLen n) 0 := rfl
  rw [hstep, iterate_prgQueryStep (x n) [], bind_map_left]
  simp only [List.nil_append]

private theorem isOraclePPTOn_prgQueryStep {outLen : ℕ → ℕ}
    (hout : ComputableInPolyTime outLen encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary (encPair (encList encBits) encBits))
      (encPair (encList encBits) encBits)
      (fun pair : ℕ × (List (List Bool) × List Bool) => prgQueryStep outLen pair.1 pair.2) := by
  let inp : (ℕ × (List (List Bool) × List Bool)) ↪ List Bool :=
    encPair encUnary (encPair (encList encBits) encBits)
  let hfst := ComputableInPolyTime.fst encUnary (encPair (encList encBits) encBits)
  let hsnd := ComputableInPolyTime.snd encUnary (encPair (encList encBits) encBits)
  let hwords := hsnd.fst'
  let hacc0 := hsnd.snd'
  let hquery : ComputableInPolyTime
      (fun p : ℕ × (List (List Bool) × List Bool) => p.2.1.headD []) inp encBits :=
    (ComputableInPolyTime.headD []).comp hwords
  let hw0 : ComputableInPolyTime (fun p : ℕ × (List (List Bool) × List Bool) => outLen p.1)
      inp encUnary :=
    hout.comp hfst
  unfold prgQueryStep
  refine IsOraclePPTOn.cond' (by fun_prop) hsnd.isOraclePPTOn ?_
  refine (IsOraclePPTOn.query_take' () hquery hw0).map_with'
    (f := fun pair reply =>
      (pair.2.1.tail, pair.2.2 ++ (reply ++ List.replicate (outLen pair.1) false).take
        (outLen pair.1))) ?_
  let p1 := ComputableInPolyTime.fst inp encBits
  let p2 := ComputableInPolyTime.snd inp encBits
  have htail : ComputableInPolyTime
      (fun p : (ℕ × (List (List Bool) × List Bool)) × List Bool => p.1.2.1.tail)
      (encPair inp encBits) (encList encBits) := by
    fun_prop
  let hw := hw0.comp p1
  let hacc := hacc0.comp p1
  let hrep := (ComputableInPolyTime.bitsReplicate false).comp hw
  exact htail.prod (hacc.bitsAppend ((p2.bitsAppend hrep).bitsTakeWithInput hw))

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
  have heq :
      prgFromPRFReductionLoop ℓ inLen outLen x A = prgFromPRFReduction ℓ inLen outLen x A := by
    funext n input
    exact prgFromPRFReductionLoop_eq ℓ inLen outLen x A n input
  rw [← heq]
  have hℓ : ComputableInPolyTime ℓ encUnary encUnary := by
    simpa only [Function.comp_def, List.length_ofFn] using
      (ComputableInPolyTime.length_list encBits).comp hx
  have hinit : ComputableInPolyTime
      (fun n => (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), ([] : List Bool)))
      encUnary (encPair (encList encBits) encBits) :=
    hx.prod (.const [])
  have hpolyOut : PolyBounded (fun n => (encUnary n).length) outLen := by
    simpa only [encUnary_apply, List.length_replicate] using hout.polyBounded_length
  have hgrowth : ∀ n (state next : List (List Bool) × List Bool),
      next ∈ OracleComp.support (prgQueryStep outLen n state) →
      (encPair (encList encBits) encBits next).length ≤
        (encPair (encList encBits) encBits state).length + outLen n := by
    intro n state next hnext
    obtain ⟨words, acc⟩ := state
    cases words with
    | nil =>
      simp only [prgQueryStep, List.isEmpty_nil, ite_true] at hnext
      rw [OracleComp.eq_of_mem_supportWith_pure hnext]
      omega
    | cons word words =>
      simp only [prgQueryStep, List.isEmpty_cons, Bool.false_eq_true, ite_false] at hnext
      obtain ⟨reply, -, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
      rcases OracleComp.eq_of_mem_supportWith_pure hreply with rfl
      enc_len [List.tail_cons, List.length_append, List.length_take]
  have hiter : IsOraclePPTOn encUnary (encPair (encList encBits) encBits)
      (fun n => OracleComp.iterate (ℓ n) (prgQueryStep outLen n)
        (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), [])) :=
    IsOraclePPTOn.iterateWith_of_bounded_growth' hℓ hinit
      (isOraclePPTOn_prgQueryStep hout) hpolyOut hgrowth
  have hbits : IsOraclePPTOn encUnary encBits
      (fun n => Prod.snd <$> OracleComp.iterate (ℓ n) (prgQueryStep outLen n)
        (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), [])) :=
    IsOraclePPTOn.map' hiter (by fun_prop)
  have hpaired : IsOraclePPTOn encUnary (encPair encUnary encBits)
      (fun n => (fun bits => (n, bits)) <$>
        (Prod.snd <$> OracleComp.iterate (ℓ n) (prgQueryStep outLen n)
          (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), []))) :=
    hbits.keep_input
  have hsample : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => ProbOracleComp.sample (A p.1 p.2)) :=
    hA.on.isOraclePPTOn
  have hfull : IsOraclePPTOn encUnary encBool
      (fun n => do
        let bits ← Prod.snd <$> OracleComp.iterate (ℓ n) (prgQueryStep outLen n)
          (List.ofFn fun i : Fin (ℓ n) => List.ofFn (x n i), [])
        ProbOracleComp.sample (A n bits)) := by
    simpa only [bind_map_left] using hpaired.bind hsample
  exact (hfull.preprocess' (ComputableInPolyTime.fst encUnary encBits)).isOraclePPT

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
