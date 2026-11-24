/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Crypto.Computational.NaorReingold.Security
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.GGM.Security
import CslibFrontier.Crypto.Computational.GeneratorReindex
import CslibFrontier.Crypto.Computational.PseudorandomFunction.TruthTable
import CslibFrontier.Crypto.Computational.Stretch
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.BitString.UniformSplit
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.StatisticalDistance.Product
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import Mathlib.Tactic.Linarith

/-!
# Uniform `PseudorandomFunction` Instantiation of Naor–Reingold from DDH

This module connects the setup-parameterized universal-hash Naor–Reingold security theorems of
`CslibFrontier.Crypto.Computational.NaorReingold.Security` to the uniform bit-string primitives
`Cslib.Crypto.PseudorandomGenerator` and `Cslib.Crypto.PseudorandomFunction` over any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc`:

1. **Key-expanded Naor–Reingold bit-string PRF (`naorReingoldSeededPRF`,
   `DDH.pseudorandomFunction_naorReingoldSeeded`)** (paraphrase of [NaorReingold2004], Section 4.1,
   Construction 4.2 and Theorem 4.3, combined with PRG key expansion so a uniform `n`-bit secret key
   supplies both the `n + 1` modular exponents and the two-universal hash seed required by
   `Cslib.Crypto.PseudorandomFunction`): given an expanding PRG `expand : List Bool → List Bool`
   producing at least `(n + 1) * expWidth n + n * (2 * bound (desc n) + 1)` bits from an `n`-bit key
   with `expWidth n ≥ (F.order (desc n)).size + n`, `naorReingoldSeededPRF` slices `expand key` into
   `n + 1` binary exponents `α₀, α₁, …, αₙ` and a universal-hash seed and evaluates
   `naorReingoldHashedWordEval`. When `F.DDH (fun n => PMF.pure (desc n))` holds and
   `2 ^ n / F.order (desc n)` is negligible, `naorReingoldSeededPRF` satisfies
   `Cslib.Crypto.PseudorandomFunction`.
2. **Direct algebraic PRG from DDH alone (`DDH.exists_pseudorandomGenerator`)**: evaluating 1-bit
   universal-hash Naor–Reingold (`outLen = 1`, whose Leftover Hash Lemma error decays via
   `DDH.negligible_expected_inv_order` without any external order-growth hypothesis) at
   `seedLen n + 1` distinct binary inputs `Cslib.BitString.lowBits (inBits n) i` stretches a uniform
   `seedLen n`-bit seed by one bit, and `Cslib.Crypto.GeneratorReindex.pseudorandomGenerator`
   reindexes it to a `Cslib.Crypto.PseudorandomGenerator` at every seed length `n`.
3. **End-to-end `PseudorandomFunction` from DDH (`DDH.exists_naorReingoldPseudorandomFunction`,
   `DDH.exists_pseudorandomFunction`)**: amplifying the DDH PRG via
   `Cslib.Crypto.PseudorandomGenerator.amplify` instantiates `naorReingoldSeededPRF` directly from
   `F.DDH (fun n => PMF.pure (desc n))` and `Negligible (fun n => 2 ^ n / F.order (desc n))`;
   combining `DDH.exists_pseudorandomGenerator` with the Goldreich–Goldwasser–Micali construction
   `PseudorandomGenerator.exists_pseudorandomFunction` ([GGM1986]) also yields
   `∃ family, PseudorandomFunction family` from `F.DDH (fun n => PMF.pure (desc n))` alone.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldSeededPRF`: keyed bit-string family evaluating
  `naorReingoldHashedWordEval` on exponents and hash seed expanded from an `n`-bit secret key.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldSeededPRF`: polynomial-time
  evaluation of `naorReingoldSeededPRF`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.pseudorandomFunction_naorReingoldSeeded`:
  `PseudorandomFunction` security of `naorReingoldSeededPRF` from DDH, a key-expanding PRG, and
  negligible `2 ^ n / F.order (desc n)`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_pseudorandomGenerator`: existence of a uniform
  one-bit-stretch `PseudorandomGenerator` from `F.DDH (fun n => PMF.pure (desc n))` alone.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_naorReingoldPseudorandomFunction`: existence of
  parameters instantiating `naorReingoldSeededPRF` as a `PseudorandomFunction` from DDH and
  negligible `2 ^ n / F.order (desc n)`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.exists_pseudorandomFunction`: existence of a uniform
  `PseudorandomFunction` from `F.DDH (fun n => PMF.pure (desc n))` alone via
  `DDH.exists_pseudorandomGenerator` and the Goldreich–Goldwasser–Micali construction ([GGM1986]).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.10 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, and 10.11, pp. 424–426).
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1, Theorem 4.1, Lemma 4.2,
  Construction 4.2, Theorem 4.3, and Remark 4.2).
-/

public section

open scoped ENNReal NNReal Cslib.Probability.PMF

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-! ### Tape Parsing and Uniform-Tape Indistinguishability -/

private def parseNaorReingoldTape (count expWidth hashLen : ℕ) (tape : List Bool) :
    ℕ × List ℕ × List Bool :=
  let rest := tape.drop expWidth
  let α₀ := Cslib.BitString.binaryValue (tape.take expWidth)
  let αs := (Cslib.BitString.listRows count expWidth (rest.take (count * expWidth))).map
    Cslib.BitString.binaryValue
  let hashSeed := (rest.drop (count * expWidth)).take hashLen
  (α₀, αs, hashSeed)

private theorem parseNaorReingoldTape_take {count expWidth hashLen limit : ℕ}
    (hlim : expWidth + (count * expWidth + hashLen) ≤ limit) (tape : List Bool) :
    parseNaorReingoldTape count expWidth hashLen (tape.take limit) =
      parseNaorReingoldTape count expWidth hashLen tape := by
  unfold parseNaorReingoldTape
  simp only [List.take_take, List.drop_take, Nat.min_eq_left (show expWidth ≤ limit by omega),
    Nat.min_eq_left (show count * expWidth ≤ limit - expWidth by omega),
    Nat.min_eq_left (show hashLen ≤ limit - expWidth - count * expWidth by omega)]

private def evalNaorReingoldTape (inLen outLen : ℕ → ℕ) (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (n : ℕ) (tape query : List Bool) : List Bool :=
  let parsed :=
    parseNaorReingoldTape (inLen n) (expWidth n) (outLen n * (2 * bound (desc n) + 1)) tape
  F.naorReingoldHashedWordEval (outLen n) bound (desc n) parsed.2.2 parsed.1 parsed.2.1 query

private theorem evalNaorReingoldTape_take (inLen outLen : ℕ → ℕ) (desc : ℕ → F.Desc)
    (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ) {n limit : ℕ}
    (hlim : expWidth n + (inLen n * expWidth n + outLen n * (2 * bound (desc n) + 1)) ≤ limit)
    (tape query : List Bool) :
    F.evalNaorReingoldTape inLen outLen desc bound expWidth n (tape.take limit) query =
      F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape query := by
  unfold evalNaorReingoldTape
  rw [parseNaorReingoldTape_take hlim]

private theorem computableInPolyTime_parseNaorReingoldTape {α : Type} {input : α ↪ List Bool}
    {count expWidth hashLen : α → ℕ} {tape : α → List Bool}
    (hcount : ComputableInPolyTime count input encUnary)
    (hexp : ComputableInPolyTime expWidth input encUnary)
    (hhash : ComputableInPolyTime hashLen input encUnary)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime
      (fun a => parseNaorReingoldTape (count a) (expWidth a) (hashLen a) (tape a))
      input (encPair encNat (encPair (encList encNat) encBits)) := by
  unfold parseNaorReingoldTape
  fun_prop

private theorem computableInPolyTime_naorReingoldHashedWordEval_comp {F : PrimeOrderGroupFamily}
    {α : Type} {enc : α ↪ List Bool} {bound : F.Desc → ℕ}
    {outLen : α → ℕ} {d : α → F.Desc} {seed : α → List Bool} {α₀ : α → ℕ}
    {αs : α → List ℕ} {xs : α → List Bool}
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hout : ComputableInPolyTime outLen enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hseed : ComputableInPolyTime seed enc encBits)
    (hα₀ : ComputableInPolyTime α₀ enc encNat)
    (hαs : ComputableInPolyTime αs enc (encList encNat))
    (hxs : ComputableInPolyTime xs enc encBits) :
    ComputableInPolyTime
      (fun a =>
        F.naorReingoldHashedWordEval (outLen a) bound (d a) (seed a) (α₀ a) (αs a) (xs a))
      enc encBits :=
  (F.computableInPolyTime_naorReingoldHashedWordEval hbound).comp
    (hout.prod (hd.prod (hseed.prod (hα₀.prod (hαs.prod hxs)))))

attribute [local fun_prop]
  computableInPolyTime_parseNaorReingoldTape
  computableInPolyTime_naorReingoldHashedWordEval_comp

private theorem computableInPolyTime_evalNaorReingoldTape_of {F : PrimeOrderGroupFamily}
    {α : Type} {input : α ↪ List Bool}
    {inLen outLen : ℕ → ℕ} {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth : ℕ → ℕ}
    {param : α → ℕ} {tape query : α → List Bool}
    (hinLen : ComputableInPolyTime inLen encUnary encUnary)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexp : ComputableInPolyTime expWidth encUnary encUnary)
    (hparam : ComputableInPolyTime param input encUnary)
    (htape : ComputableInPolyTime tape input encBits)
    (hquery : ComputableInPolyTime query input encBits) :
    ComputableInPolyTime
      (fun a => F.evalNaorReingoldTape inLen outLen desc bound expWidth
        (param a) (tape a) (query a))
      input encBits := by
  have hd : ComputableInPolyTime (fun a => desc (param a)) input F.encDesc := hdesc.comp hparam
  have hparsed := computableInPolyTime_parseNaorReingoldTape
    (hinLen.comp hparam) (hexp.comp hparam)
    ((houtLen.comp hparam).unary_mul'
      (((ComputableInPolyTime.const 2).unary_mul' (hbound.comp hd)).unary_add' (.const 1))) htape
  unfold evalNaorReingoldTape
  exact computableInPolyTime_naorReingoldHashedWordEval_comp hbound (houtLen.comp hparam) hd
    (hparsed.snd'.snd') hparsed.fst' (hparsed.snd'.fst') hquery

attribute [local fun_prop] computableInPolyTime_evalNaorReingoldTape_of

private noncomputable def binaryZModLaw (width q : ℕ) : PMF (ZMod q) :=
  ((Cslib.BitString.uniformList width).map Cslib.BitString.binaryValue).map Nat.cast

private theorem dist_binaryZModLaw_le {s width q : ℕ} [NeZero q]
    (hw : q.size + s ≤ width) :
    dist (binaryZModLaw width q) (PMF.uniformOfFintype (ZMod q)) ≤ 1 / 2 ^ s := by
  have heq : binaryZModLaw width q =
      (ProbComp.eval (ProbComp.sampleModNat width q)).map Nat.cast := by
    unfold binaryZModLaw
    simp only [pmf_norm, ProbComp.sampleModNat, ProbComp.sampleBinaryNat,
      Cslib.BitString.eval_sampleList, ZMod.natCast_mod]
  rw [heq]
  have hlt : (q : ℝ) < (2 : ℝ) ^ q.size := by exact_mod_cast Nat.lt_size_self q
  calc dist ((ProbComp.eval (ProbComp.sampleModNat width q)).map (Nat.cast : ℕ → ZMod q))
        (PMF.uniformOfFintype (ZMod q))
      ≤ (q : ℝ) / (2 : ℝ) ^ width := ProbComp.dist_map_natCast_eval_sampleModNat_le width q
    _ ≤ (2 : ℝ) ^ q.size / (2 : ℝ) ^ (q.size + s) :=
        div_le_div₀ (by positivity) hlt.le (by positivity) (pow_le_pow_right₀ (by norm_num) hw)
    _ = 1 / 2 ^ s := by rw [pow_add, div_mul_eq_div_div, div_self (by positivity)]

private theorem uniformList_map_parseNaorReingoldTape (count expWidth hashLen : ℕ) :
    (Cslib.BitString.uniformList (expWidth + (count * expWidth + hashLen))).map
      (parseNaorReingoldTape count expWidth hashLen) =
    ((Cslib.BitString.uniformList expWidth).map Cslib.BitString.binaryValue).bind fun α₀ =>
      ((PMF.iid ((Cslib.BitString.uniformList expWidth).map Cslib.BitString.binaryValue) count).map
        List.ofFn).bind fun αs =>
        (Cslib.BitString.uniformList hashLen).map fun seed => (α₀, αs, seed) := by
  unfold parseNaorReingoldTape
  dsimp only
  rw [Cslib.BitString.uniformList_map_split3 expWidth (count * expWidth) hashLen
    (fun front mid back =>
      (Cslib.BitString.binaryValue front,
        (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue,
        back.take hashLen)),
    ← Cslib.BitString.uniformList_map_listRows count expWidth Cslib.BitString.binaryValue]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1 with front : 1
  congr 1 with mid : 1
  rw [show (fun s₃ : List Bool =>
      (Cslib.BitString.binaryValue front,
        (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue,
        s₃.take hashLen)) =
      (fun seed =>
        (Cslib.BitString.binaryValue front,
          (Cslib.BitString.listRows count expWidth mid).map Cslib.BitString.binaryValue, seed)) ∘
        List.take hashLen from rfl,
    ← PMF.map_comp, Cslib.BitString.uniformList_take le_rfl]

private theorem advantage_evalNaorReingoldTape_uniform_le (inLen outLen : ℕ → ℕ)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ)
    (hexp : (F.order (desc n)).size + n ≤ expWidth n) :
    Game.advantage
      ((Cslib.BitString.uniformList
        (expWidth n + (inLen n * expWidth n + outLen n * (2 * bound (desc n) + 1)))).bind
        fun tape =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = inLen n then
                F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape request.2
              else []))
            (adversary n []))
      (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inLen outLen bound
        (fun k _ => adversary k []) n) ≤
      ((inLen n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  let m := inLen n
  let ℓ := outLen n
  let d := desc n
  let E := expWidth n
  let H := ℓ * (2 * bound d + 1)
  have : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩
  let detRun : ZMod (F.order d) × (Fin m → ZMod (F.order d)) → PMF Bool := fun p =>
    (Cslib.BitString.uniformList H).bind fun seed =>
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = m then
            F.linearHashKDF (fun _ => ℓ) bound
              ((d, seed), F.encode d (F.naorReingoldEval d p.1 p.2
                (BitString.ofList m request.2)))
          else []))
        (adversary n [])
  let μ : PMF (ZMod (F.order d)) := binaryZModLaw E (F.order d)
  let ν : PMF (ZMod (F.order d)) := PMF.uniformOfFintype (ZMod (F.order d))
  have hlhs :
      ((Cslib.BitString.uniformList (E + (m * E + H))).bind fun tape =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = m then
              F.evalNaorReingoldTape inLen outLen desc bound expWidth n tape request.2
            else []))
          (adversary n [])) =
      (μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)).bind detRun := by
    have hparse := congrArg
      (fun law : PMF (ℕ × List ℕ × List Bool) =>
        law.bind fun parsed =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle fun request =>
              PMF.pure (if request.2.length = m then
                F.naorReingoldHashedWordEval ℓ bound d parsed.2.2 parsed.1 parsed.2.1 request.2
              else []))
            (adversary n []))
      (uniformList_map_parseNaorReingoldTape m E H)
    rw [PMF.bind_map] at hparse
    refine Eq.trans hparse ?_
    dsimp only [μ, binaryZModLaw, detRun]
    simp only [pmf_norm, PMF.iid_map]
    congr 1 with a₀ : 1; congr 1 with aVec : 1; congr 1 with seed : 1; congr 1 with q : 1
    cases q with
    | inl _ => rfl
    | inr request =>
      dsimp only [OracleComp.sumHandler]
      by_cases hq : request.2.length = m
      · simp only [hq, ↓reduceIte, naorReingoldHashedWordEval]
        have heval := F.naorReingoldWordEval_eq_encode d (Cslib.BitString.binaryValue a₀)
          (fun i => Cslib.BitString.binaryValue (aVec i)) (BitString.ofList m request.2)
        rw [BitString.ofFn_ofList hq] at heval
        rw [heval]
      · simp [hq]
  have hrhs :
      F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inLen outLen bound
        (fun k _ => adversary k []) n =
      (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)).bind detRun := by
    simp only [pmf_norm, naorReingoldHashedRealGame, seededSetup, linearHashSeedLen]
    change ((Cslib.BitString.uniformList H).bind fun seed =>
      ν.bind fun α₀ => (PMF.uniformOfFintype (Fin m → ZMod (F.order d))).bind fun α => _) =
      ν.bind fun α₀ => (PMF.iid ν m).bind fun α => detRun (α₀, α)
    rw [PMF.bind_comm (Cslib.BitString.uniformList H) ν]
    congr 1 with α₀ : 1
    rw [PMF.bind_comm (Cslib.BitString.uniformList H)
      (PMF.uniformOfFintype (Fin m → ZMod (F.order d))), ← PMF.iid_uniformOfFintype m]
  change Game.advantage
    ((Cslib.BitString.uniformList (E + (m * E + H))).bind _)
    (F.naorReingoldHashedRealGame _ _ _ _ _ n) ≤ _
  rw [hlhs, hrhs, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hswap (p : PMF (ZMod (F.order d))) (q : PMF (Fin m → ZMod (F.order d))) :
      (p.bind fun α₀ => q.map (α₀, ·)) = (q.bind fun α => p.map (·, α)) := by
    simp only [PMF.map]; exact PMF.bind_comm p q _
  calc dist ((μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)).bind detRun)
        ((ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)).bind detRun)
      ≤ dist (μ.bind fun α₀ => (PMF.iid μ m).map (α₀, ·))
          (ν.bind fun α₀ => (PMF.iid μ m).map (α₀, ·)) +
          dist (ν.bind fun α₀ => (PMF.iid μ m).map (α₀, ·))
            (ν.bind fun α₀ => (PMF.iid ν m).map (α₀, ·)) :=
        (PMF.dist_bind_le _ _ _).trans (dist_triangle _ _ _)
    _ ≤ dist μ ν + m * dist μ ν := by
        refine add_le_add (PMF.dist_bind_le _ _ _) ?_
        rw [hswap ν (PMF.iid μ m), hswap ν (PMF.iid ν m)]
        exact (PMF.dist_bind_le _ _ _).trans (PMF.dist_iid_le μ ν m)
    _ = (m + 1 : ℝ) * dist μ ν := by ring
    _ ≤ (m + 1 : ℝ) * (1 / 2 ^ n) :=
        mul_le_mul_of_nonneg_left (dist_binaryZModLaw_le hexp) (by positivity)
    _ = ((((m + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by push_cast; ring

private theorem naorReingoldHashedIdealGame_pure_const (inLen outLen : ℕ → ℕ)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) inLen outLen bound
      (fun k _ => adversary k []) n =
    (PMF.uniformOfFintype (BitString (inLen n) → BitString (outLen n))).bind fun f =>
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = inLen n then
            List.ofFn (f (BitString.ofList (inLen n) request.2))
          else []))
        (adversary n []) := by
  simp only [naorReingoldHashedIdealGame, PMF.monad_bind_eq_bind, PMF.bind_const]

/-! ### Key-Expanded Naor–Reingold `PseudorandomFunction` -/

/-- Keyed bit-string family evaluating the universal-hash Naor–Reingold construction
`naorReingoldHashedWordEval` after expanding `key` via `expand` into `key.length + 1`
`expWidth key.length`-bit binary exponents and a
`key.length * (2 * bound (desc key.length) + 1)`-bit two-universal hash seed (paraphrase of
[NaorReingold2004], Section 4.1, Construction 4.2, combined with PRG key expansion so a uniform
`n`-bit secret key suffices for `Cslib.Crypto.PseudorandomFunction`). -/
@[expose] def naorReingoldSeededPRF (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (expand : List Bool → List Bool)
    (key query : List Bool) : List Bool :=
  let n := key.length
  let E := expWidth n
  let H := n * (2 * bound (desc n) + 1)
  let tape := expand key
  let rest := tape.drop E
  let α₀ := Cslib.BitString.binaryValue (tape.take E)
  let αs := (Cslib.BitString.listRows n E (rest.take (n * E))).map Cslib.BitString.binaryValue
  let hashSeed := (rest.drop (n * E)).take H
  F.naorReingoldHashedWordEval n bound (desc n) hashSeed α₀ αs query

/-- `naorReingoldSeededPRF` always outputs a bit string of length `key.length`. -/
@[simp] theorem length_naorReingoldSeededPRF (desc : ℕ → F.Desc) (bound : F.Desc → ℕ)
    (expWidth : ℕ → ℕ) (expand : List Bool → List Bool) (key query : List Bool) :
    (F.naorReingoldSeededPRF desc bound expWidth expand key query).length = key.length := by
  simp [naorReingoldSeededPRF]

/-- `naorReingoldSeededPRF` is computable in deterministic polynomial time when `desc`, `bound`,
`expWidth`, and `expand` are polynomial-time computable. -/
theorem computableInPolyTime_naorReingoldSeededPRF {desc : ℕ → F.Desc} {bound : F.Desc → ℕ}
    {expWidth : ℕ → ℕ} {expand : List Bool → List Bool}
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexpWidth : ComputableInPolyTime expWidth encUnary encUnary)
    (hexpand : ComputableInPolyTime expand encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool =>
        F.naorReingoldSeededPRF desc bound expWidth expand p.1 p.2)
      (encPair encBits encBits) encBits := by
  change ComputableInPolyTime
    (fun p : List Bool × List Bool =>
      F.evalNaorReingoldTape id id desc bound expWidth p.1.length (expand p.1) p.2)
    (encPair encBits encBits) encBits
  fun_prop

private noncomputable def prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) : Distinguisher :=
  fun n tape =>
    Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler (fun r => StateT.lift (ProbComp.unifFin r))
        fun request _ =>
          pure (if request.2.length = n then
            F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
          else [], ()))
      (adversary n [])).run ()

private theorem isPPT_prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth : ℕ → ℕ}
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexpWidth : ComputableInPolyTime expWidth encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPT encBool (prfTapeDistinguisher F desc bound expWidth adversary) := by
  let ECaller := encPair encUnary encBits
  let EHandler := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hhandler : IsPPTOn EHandler (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool) × (Unit × List Bool) × Unit =>
        pure (if p.2.1.2.length = p.1.1 then
          F.evalNaorReingoldTape id id desc bound expWidth p.1.1 p.1.2 p.2.1.2
        else [], ())) := by
    refine (IsPPTOn.ite
      (condition := fun p : (ℕ × List Bool) × (Unit × List Bool) × Unit => p.2.1.2.length = p.1.1)
      (yes := fun p =>
        pure (F.evalNaorReingoldTape id id desc bound expWidth p.1.1 p.1.2 p.2.1.2, ()))
      (no := fun _ => pure ([], ()))
      (by fun_prop)
      ((computableInPolyTime_evalNaorReingoldTape_of .id' .id' hdesc hbound hexpWidth
        (by fun_prop) (by fun_prop) (by fun_prop)).prod (.const ())).isPPTOn
      (by fun_prop)).congr fun p => ?_
    by_cases h : p.2.1.2.length = p.1.1 <;> simp [h]
  unfold prfTapeDistinguisher
  refine (hadversary.run_interpret_preprocess (input := ECaller) (State := Unit)
    (stateEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool) (request : Unit × List Bool) (_ : Unit) =>
      pure (if request.2.length = p.1 then
        F.evalNaorReingoldTape id id desc bound expWidth p.1 p.2 request.2
      else [], ()))
    (prepare := fun p : ℕ × List Bool => (p.1, []))
    (initial := fun _ => ()) (resources := fun p _ => p.1)
    (by fun_prop) hhandler (by fun_prop) (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    (fun a request _ _ result hresult => by
      simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      refine ⟨trivial, ?_, Nat.le_add_right _ _⟩
      by_cases hq : request.2.length = a.1
      · simp only [hq, ↓reduceIte]; unfold evalNaorReingoldTape; simp
      · simp [hq])).map (ComputableInPolyTime.fst encBool (encFinEnum Unit))

private theorem eval_prfTapeDistinguisher (F : PrimeOrderGroupFamily)
    (desc : ℕ → F.Desc) (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ)
    (adversary : OracleDistinguisher) (n : ℕ) (tape : List Bool) :
    ProbComp.eval (prfTapeDistinguisher F desc bound expWidth adversary n tape) =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request =>
          PMF.pure (if request.2.length = n then
            F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
          else []))
        (adversary n []) := by
  unfold prfTapeDistinguisher
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  have hrw := ProbOracleComp.run_interpret_readOnly
    (fun (request : Unit × List Bool) (_ : Unit) =>
      PMF.pure (if request.2.length = n then
        F.evalNaorReingoldTape id id desc bound expWidth n tape request.2 else []))
    (adversary n []) ()
  simp only [ProbComp.eval_pure, PMF.pure_map] at hrw ⊢
  rw [hrw, PMF.map_comp]
  exact PMF.map_id _

private theorem isOraclePPT_const_nil {adv : OracleDistinguisher}
    (hadv : IsOraclePPT encBool adv) :
    IsOraclePPT encBool (fun k (_ : List Bool) => adv k []) :=
  (hadv.on.preprocess (prepare := fun p : ℕ × List Bool => (p.1, [])) (by fun_prop)).isOraclePPT

private theorem negligible_naorReingoldHashedGame_ideal_pure {F : PrimeOrderGroupFamily}
    {desc : ℕ → F.Desc} {bound : F.Desc → ℕ}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hbound : ∀ n, ∀ x : F.Carrier (desc n), (F.encode (desc n) x).length ≤ bound (desc n))
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (F.order (desc n) : ℝ≥0))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
          (fun k _ => adversary k []) n)
        (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
          (fun k _ => adversary k []) n) :=
  hDDH.negligible_naorReingoldHashedGame_ideal (inLen := id) (outLen := id)
    (descBound := fun n => (F.encDesc (desc n)).length) (qMin := fun n => F.order (desc n))
    .id' .id' hbound_poly
    ((ComputableInPolyTime.encoding_length F.encDesc).comp hdesc).polynomiallyBounded
    (fun _ _ hd => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact le_rfl)
    (fun n _ hd => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact hbound n)
    (fun n => (F.prime_order (desc n)).pos)
    (fun _ _ hd => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact le_rfl)
    hneg (isOraclePPT_const_nil hadversary)

/-- **Uniform `PseudorandomFunction` security of `naorReingoldSeededPRF`** (paraphrase of
[NaorReingold2004], Section 4.1, Construction 4.2 and Theorem 4.3, combined with PRG key
expansion): if `desc : ℕ → F.Desc` is a deterministic polynomial-time group family satisfying
`F.DDH (fun n => PMF.pure (desc n))` with `2 ^ n / F.order (desc n)` negligible, `expWidth n ≥
(F.order (desc n)).size + n`, and `expand` is a `PseudorandomGenerator` stretching `n`-bit keys to
at least `(n + 1) * expWidth n + n * (2 * bound (desc n) + 1)` bits, then `naorReingoldSeededPRF`
is a uniform `PseudorandomFunction`. -/
theorem DDH.pseudorandomFunction_naorReingoldSeeded {F : PrimeOrderGroupFamily}
    {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth targetLen : ℕ → ℕ}
    {expand : List Bool → List Bool}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hbound : ∀ n, ∀ x : F.Carrier (desc n), (F.encode (desc n) x).length ≤ bound (desc n))
    (hexpWidth_poly : ComputableInPolyTime expWidth encUnary encUnary)
    (hexpWidth : ∀ n, (F.order (desc n)).size + n ≤ expWidth n)
    (hexpand : PseudorandomGenerator expand targetLen)
    (htarget : ∀ n, (n + 1) * expWidth n + n * (2 * bound (desc n) + 1) ≤ targetLen n)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (F.order (desc n) : ℝ≥0)) :
    PseudorandomFunction (F.naorReingoldSeededPRF desc bound expWidth expand) := by
  refine ⟨F.computableInPolyTime_naorReingoldSeededPRF hdesc hbound_poly hexpWidth_poly
    hexpand.polyTime, fun key query _ => F.length_naorReingoldSeededPRF _ _ _ _ key query, ?_⟩
  intro adversary hadversary
  let D_tape := prfTapeDistinguisher F desc bound expWidth adversary
  have hprg_neg := hexpand.indistinguishable D_tape
    (isPPT_prfTapeDistinguisher F hdesc hbound_poly hexpWidth_poly hadversary)
  have hnr_neg := negligible_naorReingoldHashedGame_ideal_pure hDDH hdesc hbound_poly hbound hneg
    hadversary
  have hexp_neg : Negligible fun n => ((n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by negligible
  refine negligible_of_le ((hprg_neg.add hexp_neg).add hnr_neg) fun n => ?_
  let need := expWidth n + (n * expWidth n + n * (2 * bound (desc n) + 1))
  have hneed_le : need ≤ targetLen n := by have := htarget n; dsimp only [need]; linarith
  have hreal_eq :
      ProbComp.eval (prfRealGame id (F.naorReingoldSeededPRF desc bound expWidth expand)
        adversary n) =
      distinguishingGame (generatorEnsemble expand n) (D_tape n) := by
    simp only [pmf_norm, prfRealGame, id_eq, ProbOracleComp.run, distinguishingGame_eq_bind,
      generatorEnsemble, ProbOracleComp.eval_interpret, BitString.eval_sampleList, D_tape,
      eval_prfTapeDistinguisher]
    refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
    have hklen : key.length = n := BitString.length_of_mem_support_uniformList hkey
    congr 1 with q : 1
    cases q with
    | inl _ => rfl
    | inr request =>
      dsimp only [OracleComp.sumHandler, prfOracle]
      by_cases hq : request.2.length = n
      · simp only [hq, ↓reduceIte]
        change PMF.pure (F.evalNaorReingoldTape id id desc bound expWidth key.length
          (expand key) request.2) = _
        rw [hklen]
      · simp [hq]
  have hunif_trunc :
      distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n) =
      (BitString.uniformList need).bind fun tape =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun request =>
            PMF.pure (if request.2.length = n then
              F.evalNaorReingoldTape id id desc bound expWidth n tape request.2
            else []))
          (adversary n []) := by
    rw [← BitString.uniformList_take hneed_le]
    simp only [pmf_norm, distinguishingGame_eq_bind, D_tape, eval_prfTapeDistinguisher]
    congr 1 with x : 1; congr 1 with q : 1
    cases q with
    | inl _ => rfl
    | inr request =>
      dsimp only [OracleComp.sumHandler]
      rw [evalNaorReingoldTape_take F id id desc bound expWidth (limit := need) le_rfl]
  have hideal_eq :
      ProbComp.eval (prfIdealGame id id adversary n) =
      F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) id id bound
        (fun k _ => adversary k []) n := by
    rw [naorReingoldHashedIdealGame_pure_const]
    simp only [prfIdealGame, id_eq, ProbOracleComp.run, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.eval_interpret, ProbComp.eval_pure, randomFunctionOracle]
  dsimp only [Pi.add_apply]
  rw [hreal_eq, hideal_eq]
  game_trans [distinguishingGame (BitString.uniformList (targetLen n)) (D_tape n),
    F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) id id bound
      (fun k _ => adversary k []) n]
    using [le_rfl, hunif_trunc.symm ▸ advantage_evalNaorReingoldTape_uniform_le F id id desc bound
      expWidth adversary n (hexpWidth n), le_rfl]
  exact le_rfl

/-! ### Direct Algebraic `PseudorandomGenerator` from DDH Alone -/

private theorem sq_add_six_mul_add_seven_le_two_pow :
    ∀ s : ℕ, s * s + 6 * s + 7 ≤ 2 ^ (s + 4)
  | 0 => by norm_num
  | 1 => by norm_num
  | k + 2 => by
      have ih := sq_add_six_mul_add_seven_le_two_pow (k + 1)
      have hpow : 2 ^ (k + 2 + 4) = 2 * 2 ^ (k + 1 + 4) := by
        rw [show k + 2 + 4 = (k + 1 + 4) + 1 by omega, Nat.pow_succ']
      nlinarith

private theorem seedLen_succ_le_two_pow (e h : ℕ) :
    e + ((e + h + 4) * e + h) + 1 ≤ 2 ^ (e + h + 4) := by
  have h1 := sq_add_six_mul_add_seven_le_two_pow (e + h)
  have h2 : e + ((e + h + 4) * e + h) + 1 ≤ (e + h) * (e + h) + 6 * (e + h) + 7 := by nlinarith
  simpa only [Nat.add_assoc] using h2.trans h1

private theorem uniformOfFintype_map_lowBits_randomFunction {r M : ℕ} (hM : M ≤ 2 ^ r) :
    (PMF.uniformOfFintype (BitString r → BitString 1)).map
      (fun f => ((List.range M).map (Cslib.BitString.lowBits r)).map fun word =>
        (if word.length = r then List.ofFn (f (BitString.ofList r word)) else []).headD false) =
    BitString.uniformList M := by
  let x : Fin M ↪ BitString r :=
    ⟨fun j => BitString.ofList r (Cslib.BitString.lowBits r j.val), fun a b h => by
      ext
      exact Cslib.BitString.lowBits_injective_of_lt (a.2.trans_le hM) (b.2.trans_le hM)
        (by simpa [BitString.ofFn_ofList (Cslib.BitString.length_lowBits r _)] using
          congrArg List.ofFn h)⟩
  have hpref := Cslib.BitString.uniformOfFintype_map_readPrefixes x (fun _ => 1) (fun _ => le_rfl)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hpref
  refine Eq.trans ?_ hpref
  congr 1; funext f
  have hflat : (List.ofFn fun i : Fin M => (List.ofFn (f (x i))).take 1).flatten =
      List.ofFn (fun i : Fin M => f (x i) ⟨0, Nat.zero_lt_one⟩) := by
    have hrow (i : Fin M) : (List.ofFn (f (x i))).take 1 = [f (x i) ⟨0, Nat.zero_lt_one⟩] := by
      simp [List.ofFn_succ, List.ofFn_zero]
    have hsing (l : List Bool) : (l.map fun b => [b]).flatten = l := by
      induction l <;> simp [*]
    simp_rw [hrow]
    simpa only [List.map_ofFn, Function.comp_def] using
      hsing (List.ofFn fun i : Fin M => f (x i) ⟨0, Nat.zero_lt_one⟩)
  rw [hflat]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have hi : i < M := by simpa using h₂
  simp only [List.getElem_map, List.getElem_range, Cslib.BitString.length_lowBits, ↓reduceIte,
    List.ofFn_succ, List.ofFn_zero, List.headD_cons, List.getElem_ofFn]
  rfl

private theorem exists_poly_encode_bound (F : PrimeOrderGroupFamily) :
    ∃ bound : F.Desc → ℕ,
      ComputableInPolyTime bound F.encDesc encUnary ∧
      ∀ d : F.Desc, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d := by
  obtain ⟨cB, eB, hbound⟩ := F.exists_length_encode_le
  exact ⟨fun d => cB * ((F.encDesc d).length + 1) ^ eB, by fun_prop, hbound⟩

private def ddhPRGCore (F : PrimeOrderGroupFamily) (inBits : ℕ → ℕ) (desc : ℕ → F.Desc)
    (bound : F.Desc → ℕ) (expWidth seedLen : ℕ → ℕ) (n : ℕ) (seed : List Bool) : List Bool :=
  (List.range (seedLen n + 1)).map fun i =>
    (F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n seed
      (Cslib.BitString.lowBits (inBits n) i)).headD false

private theorem computableInPolyTime_ddhPRGCore (F : PrimeOrderGroupFamily)
    {inBits : ℕ → ℕ} {desc : ℕ → F.Desc} {bound : F.Desc → ℕ} {expWidth seedLen : ℕ → ℕ}
    (hinBits : ComputableInPolyTime inBits encUnary encUnary)
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary)
    (hexp : ComputableInPolyTime expWidth encUnary encUnary)
    (hcnt : ComputableInPolyTime (fun p : ℕ × List Bool => seedLen p.1 + 1)
      (encPair encUnary encBits) encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool =>
      ddhPRGCore F inBits desc bound expWidth seedLen p.1 p.2)
      (encPair encUnary encBits) encBits := by
  unfold ddhPRGCore
  exact ComputableInPolyTime.mapToBitsWithInput (ComputableInPolyTime.range.comp hcnt)
    (by fun_prop)

private theorem isOraclePPT_ddhPRGAdv {inBits seedLen : ℕ → ℕ} {D : Distinguisher}
    (hinBits : ComputableInPolyTime inBits encUnary encUnary)
    (hcnt : ComputableInPolyTime (fun p : ℕ × List Bool => seedLen p.1 + 1)
      (encPair encUnary encBits) encUnary)
    (hD : IsPPT encBool D) :
    IsOraclePPT encBool (fun n (_ : List Bool) => do
      let word ← KabanetsCai.queryTable
        ((List.range (seedLen n + 1)).map (Cslib.BitString.lowBits (inBits n)))
      ProbOracleComp.sample (D n word)) := by
  have hqueries : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        (List.range (seedLen p.1 + 1)).map (Cslib.BitString.lowBits (inBits p.1)))
      (encPair encUnary encBits) (encList encBits) :=
    ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hcnt) (by fun_prop)
  exact ((KabanetsCai.isOraclePPTOn_queryTable.preprocess hqueries).bind_with
    (second := fun p word => ProbOracleComp.sample (D p.1 word))
    ((hD.on.preprocess
      (input := encPair (encPair encUnary encBits) encBits)
      (prepare := fun q : (ℕ × List Bool) × List Bool => (q.1.1, q.2))
      (by fun_prop)).isOraclePPTOn)).isOraclePPT

private theorem negligible_naorReingoldHashedGame_ideal_const_pure {F : PrimeOrderGroupFamily}
    {inBits : ℕ → ℕ} {desc : ℕ → F.Desc} {bound : F.Desc → ℕ}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hinBits : ComputableInPolyTime inBits encUnary encUnary)
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hbound : ∀ d : F.Desc, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    {adv : OracleDistinguisher} (hadv : IsOraclePPT encBool adv) :
    Negligible fun n =>
      Game.advantage
        (F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
          (fun k _ => adv k []) n)
        (F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
          (fun k _ => adv k []) n) :=
  hDDH.negligible_naorReingoldHashedGame_ideal_const 1 hinBits hbound_poly
    ((ComputableInPolyTime.encoding_length F.encDesc).comp hdesc).polynomiallyBounded
    (fun _ _ hd => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact le_rfl)
    (fun n _ hd x => by rw [PMF.mem_support_pure_iff] at hd; subst hd; exact hbound (desc n) x)
    (isOraclePPT_const_nil hadv)

/-- **Existence of a uniform `PseudorandomGenerator` from DDH alone**: for any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))`, evaluating 1-bit universal-hash Naor–Reingold at distinct
binary inputs and reindexing via `GeneratorReindex.pseudorandomGenerator` yields a uniform
`PseudorandomGenerator` with one-bit stretch at every seed length. -/
theorem DDH.exists_pseudorandomGenerator {F : PrimeOrderGroupFamily} {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc) :
    ∃ generator : List Bool → List Bool, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨bound, hbound_poly, hbound⟩ := exists_poly_encode_bound F
  let expWidth : ℕ → ℕ := fun n => (F.order (desc n)).size + n + 1
  let hashLen : ℕ → ℕ := fun n => 2 * bound (desc n) + 1
  let inBits : ℕ → ℕ := fun n => expWidth n + hashLen n + 4
  let seedLen : ℕ → ℕ := fun n => expWidth n + (inBits n * expWidth n + hashLen n)
  let core := ddhPRGCore F inBits desc bound expWidth seedLen
  have hexp_poly : ComputableInPolyTime expWidth encUnary encUnary :=
    ((ComputableInPolyTime.binary_size.comp (F.computableInPolyTime_order.comp hdesc)).unary_add'
      .id').unary_add' (.const 1)
  have hhash_poly : ComputableInPolyTime hashLen encUnary encUnary :=
    ((ComputableInPolyTime.const 2).unary_mul' (hbound_poly.comp hdesc)).unary_add' (.const 1)
  have hinBits_poly : ComputableInPolyTime inBits encUnary encUnary :=
    (hexp_poly.unary_add' hhash_poly).unary_add' (.const 4)
  have hseedLen_poly : ComputableInPolyTime seedLen encUnary encUnary :=
    hexp_poly.unary_add' ((hinBits_poly.unary_mul' hexp_poly).unary_add' hhash_poly)
  have hcnt : ComputableInPolyTime (fun p : ℕ × List Bool => seedLen p.1 + 1)
      (encPair encUnary encBits) encUnary :=
    (hseedLen_poly.comp (.fst _ _)).unary_add' (.const 1)
  have hge : ∀ n, n + 1 ≤ seedLen n := fun n => by dsimp only [seedLen, expWidth]; omega
  have hcore_poly :=
    computableInPolyTime_ddhPRGCore F hinBits_poly hdesc hbound_poly hexp_poly hcnt
  have hcore_len : ∀ n seed, seed.length = seedLen n → (core n seed).length = seedLen n + 1 := by
    intro n seed _; dsimp only [core]; unfold ddhPRGCore; simp
  have hsecure : ComputationallyIndistinguishable
      (fun n => (BitString.uniformList (seedLen n)).map (core n))
      (fun n => BitString.uniformList (seedLen n + 1)) := by
    intro D hD
    let queries : ℕ → List (List Bool) := fun n =>
      (List.range (seedLen n + 1)).map (Cslib.BitString.lowBits (inBits n))
    let adv : OracleDistinguisher := fun n _ => do
      let word ← KabanetsCai.queryTable (queries n)
      ProbOracleComp.sample (D n word)
    have hadv : IsOraclePPT encBool adv := isOraclePPT_ddhPRGAdv hinBits_poly hcnt hD
    have hnr_neg := negligible_naorReingoldHashedGame_ideal_const_pure hDDH hinBits_poly
      hdesc hbound_poly hbound hadv
    have hexp_neg : Negligible fun n => ((inBits n + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
      negligible
    refine negligible_of_le (hexp_neg.add hnr_neg) fun n => ?_
    have hinterp (oracle : List Bool → List Bool) :
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun request => PMF.pure (oracle request.2))
          (adv n []) =
        ProbComp.eval (D n ((queries n).map fun word => (oracle word).headD false)) := by
      change OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle fun request => pure (oracle request.2))
        (KabanetsCai.queryTable (queries n) >>= fun word => ProbOracleComp.sample (D n word)) = _
      rw [OracleComp.interpret_bind,
        KabanetsCai.interpret_queryTable ProbComp.unifOracle oracle (queries n),
        pure_bind, ProbOracleComp.interpret_sample]
      exact (OracleComp.evalWith_eq_interpret ProbComp.unifOracle _).symm
    have hreal_eq :
        distinguishingGame ((BitString.uniformList (seedLen n)).map (core n)) (D n) =
        (BitString.uniformList
          (expWidth n + (inBits n * expWidth n + 1 * (2 * bound (desc n) + 1)))).bind fun tape =>
            OracleComp.interpret
              (OracleComp.sumHandler ProbComp.unifOracle fun request =>
                PMF.pure (if request.2.length = inBits n then
                  F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n tape request.2
                else []))
              (adv n []) := by
      have hsl : seedLen n =
          expWidth n + (inBits n * expWidth n + 1 * (2 * bound (desc n) + 1)) := by
        simp [seedLen, hashLen]
      rw [hsl]
      simp only [pmf_norm, distinguishingGame_eq_bind]
      congr 1 with tape : 1
      rw [hinterp fun q =>
        if q.length = inBits n then
          F.evalNaorReingoldTape inBits (fun _ => 1) desc bound expWidth n tape q
        else []]
      dsimp only [core]
      unfold ddhPRGCore
      simp [queries, List.map_map, Function.comp_def, Cslib.BitString.length_lowBits]
    have hideal_eq :
        distinguishingGame (BitString.uniformList (seedLen n + 1)) (D n) =
        F.naorReingoldHashedIdealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
          (fun k _ => adv k []) n := by
      rw [naorReingoldHashedIdealGame_pure_const]
      have hfit : seedLen n + 1 ≤ 2 ^ (inBits n) := by
        simpa only [seedLen, inBits] using seedLen_succ_le_two_pow (expWidth n) (hashLen n)
      rw [← uniformOfFintype_map_lowBits_randomFunction hfit]
      simp only [pmf_norm, distinguishingGame_eq_bind]
      congr 1 with f : 1
      exact (hinterp fun q =>
        if q.length = inBits n then List.ofFn (f (BitString.ofList (inBits n) q)) else []).symm
    dsimp only [Pi.add_apply]
    rw [hreal_eq, hideal_eq]
    game_trans [F.naorReingoldHashedRealGame (fun k => PMF.pure (desc k)) inBits (fun _ => 1) bound
      (fun k _ => adv k []) n]
      using [advantage_evalNaorReingoldTape_uniform_le F inBits (fun _ => 1) desc bound expWidth
        adv n (by dsimp only [expWidth]; omega), le_rfl]
  exact ⟨GeneratorReindex.generate seedLen core,
    GeneratorReindex.pseudorandomGenerator hseedLen_poly hge hcore_poly hcore_len hsecure⟩

/-- **Existence of an explicit Naor–Reingold `PseudorandomFunction` from DDH**: for any
deterministic polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))` with `2 ^ n / F.order (desc n)` negligible, there exist
polynomial-time parameters `bound`, `expWidth`, and `expand` such that
`F.naorReingoldSeededPRF desc bound expWidth expand` is a uniform `PseudorandomFunction`. -/
theorem DDH.exists_naorReingoldPseudorandomFunction {F : PrimeOrderGroupFamily}
    {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (F.order (desc n) : ℝ≥0)) :
    ∃ (bound : F.Desc → ℕ) (expWidth : ℕ → ℕ) (expand : List Bool → List Bool),
      PseudorandomFunction (F.naorReingoldSeededPRF desc bound expWidth expand) := by
  obtain ⟨bound, hbound_poly, hbound⟩ := exists_poly_encode_bound F
  obtain ⟨G, hG⟩ := hDDH.exists_pseudorandomGenerator hdesc
  let expWidth : ℕ → ℕ := fun n => (F.order (desc n)).size + n + 1
  let targetLen : ℕ → ℕ := fun n => (n + 1) * expWidth n + n * (2 * bound (desc n) + 1)
  have hexp_poly : ComputableInPolyTime expWidth encUnary encUnary :=
    ((ComputableInPolyTime.binary_size.comp (F.computableInPolyTime_order.comp hdesc)).unary_add'
      .id').unary_add' (.const 1)
  have htarget_poly : ComputableInPolyTime targetLen encUnary encUnary :=
    ((ComputableInPolyTime.id'.unary_add' (.const 1)).unary_mul' hexp_poly).unary_add'
      (ComputableInPolyTime.id'.unary_mul'
        (((ComputableInPolyTime.const 2).unary_mul' (hbound_poly.comp hdesc)).unary_add'
          (.const 1)))
  have hexpand := hG.amplify targetLen htarget_poly
    (fun n => by dsimp only [targetLen, expWidth]; nlinarith)
  exact ⟨bound, expWidth, _,
    hDDH.pseudorandomFunction_naorReingoldSeeded hdesc hbound_poly (fun n => hbound (desc n))
      hexp_poly (fun n => by dsimp only [expWidth]; omega) hexpand (fun _ => le_rfl) hneg⟩

/-- **Existence of a uniform `PseudorandomFunction` from DDH alone**: any deterministic
polynomial-time prime-order group family `desc : ℕ → F.Desc` satisfying
`F.DDH (fun n => PMF.pure (desc n))` yields a uniform `PseudorandomFunction` by combining the
1-bit-stretch Naor–Reingold generator `DDH.exists_pseudorandomGenerator` with the
Goldreich–Goldwasser–Micali tree construction `PseudorandomGenerator.exists_pseudorandomFunction`
([GGM1986]). For the direct Naor–Reingold PRF family under `Negligible (2 ^ n / F.order (desc n))`,
see `DDH.exists_naorReingoldPseudorandomFunction`. -/
theorem DDH.exists_pseudorandomFunction {F : PrimeOrderGroupFamily} {desc : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (desc n)))
    (hdesc : ComputableInPolyTime desc encUnary F.encDesc) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family := by
  obtain ⟨G, hG⟩ := hDDH.exists_pseudorandomGenerator hdesc
  exact hG.exists_pseudorandomFunction

end PrimeOrderGroupFamily

end Cslib.Crypto
