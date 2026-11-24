/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pairing.BLS
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
public import CslibFrontier.Crypto.Computational.Signature.WordRandomOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Oracle.ReplayParameter
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.DiffieHellman.EncodingBounds
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Probability.UniformNat
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Asymptotic EUF-CMA and SUF-CMA security of native BLS signatures from co-CDH

This module proves [BonehShoup2023], Section 15.5.1, Theorem 15.1 (pp. 627–629) for the native
word-level BLS signature scheme `DecodablePairingGroupFamily.blsNativeROMScheme` against uniform
oracle-PPT word forgers (`ROMSignature.EUFCMA` and `ROMSignature.SUFCMA`) under the
co-Computational Diffie–Hellman assumption `PrimeOrderGroupFamily.CoCDH`:

* `Cslib.Crypto.PrimeOrderGroupFamily.CoCDH.eufCma_blsNativeROMScheme`: existential
  unforgeability under chosen message attack in the random-oracle model.
* `Cslib.Crypto.PrimeOrderGroupFamily.CoCDH.sufCma_blsNativeROMScheme`: strong existential
  unforgeability under chosen message attack in the random-oracle model.

## Proof structure

1. Given any uniform oracle-PPT word forger `program`, `exists_eufCmaGame_savedCoinForger` compiles
   it against `blsNativeROMScheme` into a saved-coin replay forger with a polynomial call budget
   `Qs n = savedCoinBudget c e keyC keyD n` using `exists_length_encode_le` and the caller's
   polynomial length bound on `description`.
2. Replacing `schnorrSigKeyGen` with the ideal key law costs at most `1 / 2 ^ n`
   (`closeTo_schnorrSigKeyGen`), and decoding signature queries and candidate forgeries
   (`blsDecodedForger`) reduces the native word game to `eufCmaGame (P.blsTypedROMScheme d)`.
3. Applying `succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked` with the dyadic biased
   coin `sampleDyadicCoin (Qs n) 1` (probability `1 / dyadicSize (Qs n) ≤ 1 / (Qs n + 1)` and
   `dyadicSize (Qs n) ≤ 2 * (Qs n + 1)`) gives an explicit concrete co-CDH loss `2.72 * a`.
4. Replacing uniform `ZMod q` banked exponents with `P.G₀.sampleExp n d` changes success by at
   most `(2 * Qs n + 1) / 2 ^ n` (`advantage_bind_iid_sampleExp_le`), matching the explicit
   uniform strict-PPT co-CDH adversary `blsBankedCoCDHAdversary` (`isPPT_blsBankedCoCDHAdversary`).

## Deviations from [BonehShoup2023]

* Each security parameter `n` fixes group parameters `description n : P.G₀.Desc` with
  polynomially bounded encoding length `(P.G₀.encDesc (description n)).length`, in place of an
  efficient randomized group-generation algorithm; `CoCDH` is assumed for the deterministic
  setup `fun n => PMF.pure (description n)`.
* `blsBankedCoCDHAdversary` uses the dyadic coin `sampleDyadicCoin (savedCoinBudget ...) 1` of
  bias `1 / dyadicSize (Qs n) ∈ [1 / (2 * (Qs n + 1)), 1 / (Qs n + 1)]`, yielding a concrete
  loss factor bounded by `6 * (Qs n + 1)` instead of `2.72 * (Qs n + 1)` while preserving
  asymptotic reduction tightness up to a factor of `2`.
-/

public section

namespace Cslib.Crypto

open Probability Protocols Protocols.ROMSignature
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM
open scoped ENNReal NNReal

namespace DecodablePairingGroupFamily

/-! ### Internal word-level structures for Coron's banked reduction -/

/-- A single banked `(c, ρ)` sample encoded cleanly as a pair of a coin bit and a scalar word. -/
private structure BLSBankSample where
  coin : Bool
  exponent : ℕ
  deriving DecidableEq

private enc_structure encBLSBankSample : BLSBankSample where
  coin : encBool,
  exponent : encNat

/-- Cached random-oracle table entry pairing a message/query word with its banked sample. -/
private structure BLSBankEntry where
  query : List Bool
  coin : Bool
  exponent : ℕ
  deriving DecidableEq

private enc_structure encBLSBankEntry : BLSBankEntry where
  query : encBits,
  coin : encBool,
  exponent : encNat

/-- State threaded through word-level Coron execution: query cache, signing-abort flag, and the
unconsumed tail of the presampled coin-and-exponent bank. -/
private structure BLSBankState where
  table : List BLSBankEntry
  aborted : Bool
  remaining : List BLSBankSample

private enc_structure encBLSBankState : BLSBankState where
  table : (encList encBLSBankEntry),
  aborted : encBool,
  remaining : (encList encBLSBankSample)

/-- Complete input passed into `runState` during word-level Coron simulation. -/
private structure BLSBankCaller (P : PairingGroupFamily) where
  secParam : ℕ
  groupParameters : P.G₀.Desc
  leftZeroWord : List Bool
  leftOneWord : List Bool
  rightZeroWord : List Bool
  forgerCoins : List Bool
  bank : List BLSBankSample

private enc_structure encBLSBankCaller (P : PairingGroupFamily) : BLSBankCaller P where
  secParam : encUnary,
  groupParameters : (P.G₀.encDesc),
  leftZeroWord : encBits,
  leftOneWord : encBits,
  rightZeroWord : encBits,
  forgerCoins : encBits,
  bank : (encList encBLSBankSample)

/-! ### Word-level Coron step and finish programs -/

private def coronSampleWord (P : PairingGroupFamily) (d : P.G₀.Desc) (v₀Word : List Bool)
    (s : BLSBankSample) : List Bool :=
  let masked := P.G₀.smul (d, s.exponent, P.G₀.encode d (P.G₀.generator d))
  if s.coin then P.G₀.add (d, v₀Word, masked) else masked

private def blsBankLookupEntry (table : List BLSBankEntry) (q : List Bool) : Option BLSBankEntry :=
  table.find? (fun e => q == e.query)

private def blsBankReplyWord (P : PairingGroupFamily) (d : P.G₀.Desc)
    (leftZeroWord rightZeroWord : List Bool) (isHash : Bool) (sample : BLSBankSample) :
    List Bool :=
  if isHash then coronSampleWord P d rightZeroWord sample
  else if sample.coin then P.G₀.encode d 0
  else P.G₀.smul (d, sample.exponent, leftZeroWord)

private def blsBankWordStep (P : PairingGroupFamily) (caller : BLSBankCaller P)
    (request : Bool × List Bool) (st : BLSBankState) : List Bool × BLSBankState :=
  let found := blsBankLookupEntry st.table request.2
  let sample : BLSBankSample :=
    (found.map fun e => ⟨e.coin, e.exponent⟩).getD (st.remaining.headD ⟨false, 0⟩)
  let table' :=
    if found.isSome then st.table else ⟨request.2, sample.coin, sample.exponent⟩ :: st.table
  let aborted' := st.aborted || (!request.1 && sample.coin)
  let reply := blsBankReplyWord P caller.groupParameters caller.leftZeroWord caller.rightZeroWord
    request.1 sample
  (reply, ⟨table', aborted', st.remaining.tail⟩)

private def blsBankWordHandler (P : PairingGroupFamily) (caller : BLSBankCaller P) :
    (q : Bool × List Bool) → StateT BLSBankState Id (RawWordSpec q) :=
  fun q st => blsBankWordStep P caller q st

private def blsBankWordFinish (P : DecodablePairingGroupFamily)
    (caller : BLSBankCaller P.toPairingGroupFamily)
    (msig : List Bool × List Bool) (st : BLSBankState) : List Bool :=
  let d := caller.groupParameters
  if st.aborted then P.G₀.encode d 0
  else
    let sample : BLSBankSample :=
      ((blsBankLookupEntry st.table msig.1).map fun e => ⟨e.coin, e.exponent⟩).getD
        (st.remaining.headD ⟨false, 0⟩)
    if sample.coin then
      let q := P.G₀.order d
      let sigWord := if P.isElem₀ (d, msig.2) then msig.2 else P.G₀.encode d 0
      P.G₀.add (d, sigWord, P.G₀.smul (d, q - sample.exponent % q, caller.leftZeroWord))
    else P.G₀.encode d 0

/-! ### Explicit strict-PPT banked co-CDH reduction -/

private noncomputable def blsBankReplay (P : PairingGroupFamily) {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ)
    (caller : BLSBankCaller P) : ProbComp ((List Bool × List Bool) × BLSBankState) :=
  let replayProg : WordOracleComp Bool (List Bool × List Bool) :=
    savedWordReplay machine (fun op word => ProbOracleComp.query (op, word))
      c e keyC keyD (caller.secParam, caller.leftOneWord, caller.forgerCoins)
  (replayProg.runState (fun req st => pure (blsBankWordStep P caller req st))).run
    ⟨[], false, caller.bank⟩

/-- Explicit Coron banked co-CDH reduction (`[BonehShoup2023]`, Theorem 15.1, pp. 628–629) built
from the compiled saved-coin native machine `machine` and polynomial parameters `(c, e, keyC,
keyD)`: samples the forger's coin tape `s`, `K = 2 * budget + 1` dyadic biased coins via
`sampleDyadicCoin budget 1` and approximate random exponents via `P.G₀.sampleExp n d`, runs the
replay machine once against the word-level Coron oracle, and outputs `(msig.2 - rhostar • u₀)`
when `cstar = true` and no signing query aborted. -/
noncomputable def blsBankedCoCDHAdversary (P : DecodablePairingGroupFamily)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Bool)
    (c e keyC keyD : ℕ) : P.G₀.CoCDHAdversary P.G₁ :=
  fun n d u₀ u₁ v₀ => do
    let budget := savedCoinBudget c e keyC keyD n
    let s ← BitString.sampleList budget
    let cs ← OracleComp.replicate (budget + budget + 1) (ProbComp.sampleDyadicCoin budget 1)
    let rhos ← OracleComp.replicate (budget + budget + 1) (P.G₀.sampleExp n d)
    let bank := (cs.zip rhos).map fun p => ⟨p.1, p.2⟩
    let caller : BLSBankCaller P.toPairingGroupFamily :=
      ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, s, bank⟩
    let res ← blsBankReplay P.toPairingGroupFamily machine c e keyC keyD caller
    let outWord := blsBankWordFinish P caller res.1 res.2
    return (P.decode₀ d outWord).getD 0

/-! ### Polynomial-time certificates for `blsBankedCoCDHAdversary` -/

private theorem computableInPolyTime_coronSampleWord (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × BLSBankSample => coronSampleWord P p.1 p.2.1 p.2.2)
      (encPair P.G₀.encDesc (encPair encBits encBLSBankSample)) encBits := by
  let E := encPair P.G₀.encDesc (encPair encBits encBLSBankSample)
  have hd : ComputableInPolyTime (fun p : P.G₀.Desc × List Bool × BLSBankSample => p.1)
      E P.G₀.encDesc := by fun_prop
  have hv : ComputableInPolyTime (fun p : P.G₀.Desc × List Bool × BLSBankSample => p.2.1)
      E encBits := by fun_prop
  have hc : ComputableInPolyTime (fun p : P.G₀.Desc × List Bool × BLSBankSample => p.2.2.coin)
      E encBool := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × BLSBankSample => p.2.2.exponent) E encNat := by fun_prop
  have hg₀ : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × BLSBankSample => P.G₀.encode p.1 (P.G₀.generator p.1))
      E encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_generator hd
  have hmask : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × BLSBankSample =>
        P.G₀.smul (p.1, p.2.2.exponent, P.G₀.encode p.1 (P.G₀.generator p.1))) E encBits :=
    P.G₀.computableInPolyTime_smul.comp (hd.prod (hr.prod hg₀))
  have hadd : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × BLSBankSample =>
        P.G₀.add (p.1, p.2.1,
          P.G₀.smul (p.1, p.2.2.exponent, P.G₀.encode p.1 (P.G₀.generator p.1)))) E encBits :=
    P.G₀.computableInPolyTime_add.comp (hd.prod (hv.prod hmask))
  exact (hc.ite hadd hmask).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_blsBankReplyWord (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample =>
        blsBankReplyWord P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair P.G₀.encDesc (encPair encBits (encPair encBits (encPair encBool encBLSBankSample))))
      encBits := by
  let E := encPair P.G₀.encDesc
    (encPair encBits (encPair encBits (encPair encBool encBLSBankSample)))
  have hd : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.1)
      E P.G₀.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.1)
      E encBits := by fun_prop
  have hv : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.2.1)
      E encBits := by fun_prop
  have hhash : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.2.2.1)
      E encBool := by fun_prop
  have hcoin : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.2.2.2.coin)
      E encBool := by fun_prop
  have hexp : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.2.2.2.exponent)
      E encNat := by fun_prop
  have hcoron := (computableInPolyTime_coronSampleWord P).comp
    (hd.prod (hv.prod (by fun_prop : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => p.2.2.2.2)
      E encBLSBankSample)))
  have hzero : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample => P.G₀.encode p.1 0)
      E encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd
  have hsmul : ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample =>
        P.G₀.smul (p.1, p.2.2.2.2.exponent, p.2.1)) E encBits :=
    P.G₀.computableInPolyTime_smul.comp (hd.prod (hexp.prod hu))
  exact (hhash.ite hcoron (hcoin.ite hzero hsmul)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_blsBankWordStep (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        blsBankWordStep P p.1 p.2.1 p.2.2)
      (encHandlerCall (encBLSBankCaller P) (encFinEnum Bool) encBLSBankState)
      (encPair encBits encBLSBankState) := by
  let E := encHandlerCall (encBLSBankCaller P) (encFinEnum Bool) encBLSBankState
  have hcall : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.1)
      E (encBLSBankCaller P) := by fun_prop
  have hop : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.1.1)
      E encBool := by
    have hr : ComputableInPolyTime
        (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.1)
        E (encPair (encFinEnum Bool) encBits) := by fun_prop
    exact (ComputableInPolyTime.of_finite (id : Bool → Bool) (encIn := encFinEnum Bool)
      (encOut := encBool)).comp ((ComputableInPolyTime.fst (encFinEnum Bool) encBits).comp hr)
  have hword : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.1.2)
      E encBits := by
    have hr : ComputableInPolyTime
        (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.1)
        E (encPair (encFinEnum Bool) encBits) := by fun_prop
    exact (ComputableInPolyTime.snd (encFinEnum Bool) encBits).comp hr
  have hst : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.2)
      E encBLSBankState := by fun_prop
  have hfound : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        blsBankLookupEntry p.2.2.table p.2.1.2)
      E (encOption encBLSBankEntry) := by
    dsimp only [blsBankLookupEntry]
    refine ComputableInPolyTime.findWith
      (test := fun q : List Bool × BLSBankEntry => q.1 == q.2.query)
      ?_ hword (by fun_prop)
    have h1 : ComputableInPolyTime (fun x : List Bool × BLSBankEntry => x.1)
        (encPair encBits encBLSBankEntry) encBits := by fun_prop
    have h2 : ComputableInPolyTime (fun x : List Bool × BLSBankEntry => x.2.query)
        (encPair encBits encBLSBankEntry) encBits := by fun_prop
    exact h1.beq h2
  have hsampleOpt : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        (blsBankLookupEntry p.2.2.table p.2.1.2).map
          fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample))
      E (encOption encBLSBankSample) := by
    refine ComputableInPolyTime.optionMapWithInput hfound ?_
    have he : ComputableInPolyTime
        (fun x : (BLSBankCaller P × (Bool × List Bool) × BLSBankState) × BLSBankEntry => x.2)
        (encPair E encBLSBankEntry) encBLSBankEntry := by fun_prop
    have hc : ComputableInPolyTime
        (fun x : (BLSBankCaller P × (Bool × List Bool) × BLSBankState) × BLSBankEntry => x.2.coin)
        (encPair E encBLSBankEntry) encBool := by fun_prop
    have hr : ComputableInPolyTime
        (fun x : (BLSBankCaller P × (Bool × List Bool) × BLSBankState) × BLSBankEntry =>
          x.2.exponent)
        (encPair E encBLSBankEntry) encNat := by fun_prop
    exact (encBLSBankSample_mk_polyTime hc hr).of_enc_eq fun _ => rfl
  have hdefault : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        p.2.2.remaining.headD ⟨false, 0⟩)
      E encBLSBankSample := by
    have hrem : ComputableInPolyTime
        (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.2.remaining)
        E (encList encBLSBankSample) := by fun_prop
    exact (ComputableInPolyTime.headD (encA := encBLSBankSample) ⟨false, 0⟩).comp hrem
  have hsample : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        ((blsBankLookupEntry p.2.2.table p.2.1.2).map
          fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
          (p.2.2.remaining.headD ⟨false, 0⟩))
      E encBLSBankSample :=
    ComputableInPolyTime.optionGetDWithInput hsampleOpt hdefault
  have hnewEntry : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        (⟨p.2.1.2,
          (((blsBankLookupEntry p.2.2.table p.2.1.2).map
            fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
            (p.2.2.remaining.headD ⟨false, 0⟩)).coin,
          (((blsBankLookupEntry p.2.2.table p.2.1.2).map
            fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
            (p.2.2.remaining.headD ⟨false, 0⟩)).exponent⟩ : BLSBankEntry))
      E encBLSBankEntry := by
    have hsc : ComputableInPolyTime (fun p => ((((blsBankLookupEntry p.2.2.table p.2.1.2).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
        (p.2.2.remaining.headD ⟨false, 0⟩))).coin) E encBool :=
      (by fun_prop : ComputableInPolyTime BLSBankSample.coin encBLSBankSample encBool).comp hsample
    have hsr : ComputableInPolyTime (fun p => ((((blsBankLookupEntry p.2.2.table p.2.1.2).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
        (p.2.2.remaining.headD ⟨false, 0⟩))).exponent) E encNat :=
      (by fun_prop : ComputableInPolyTime BLSBankSample.exponent encBLSBankSample encNat).comp
        hsample
    exact (encBLSBankEntry_mk_polyTime hword hsc hsr).of_enc_eq fun _ => rfl
  have htable0 : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.2.table)
      E (encList encBLSBankEntry) := by fun_prop
  have htable' : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        if (blsBankLookupEntry p.2.2.table p.2.1.2).isSome then p.2.2.table
        else ⟨p.2.1.2,
          (((blsBankLookupEntry p.2.2.table p.2.1.2).map
            fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
            (p.2.2.remaining.headD ⟨false, 0⟩)).coin,
          (((blsBankLookupEntry p.2.2.table p.2.1.2).map
            fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
            (p.2.2.remaining.headD ⟨false, 0⟩)).exponent⟩ :: p.2.2.table)
      E (encList encBLSBankEntry) := by
    have hisSome : ComputableInPolyTime
        (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
          (blsBankLookupEntry p.2.2.table p.2.1.2).isSome)
        E encBool :=
      ComputableInPolyTime.optionIsSome hfound
    exact (hisSome.ite htable0
      ((ComputableInPolyTime.cons encBLSBankEntry).comp (hnewEntry.prod htable0))).of_enc_eq
      fun _ => rfl
  have haborted' : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        p.2.2.aborted || (!p.2.1.1 &&
          (((blsBankLookupEntry p.2.2.table p.2.1.2).map
            fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
            (p.2.2.remaining.headD ⟨false, 0⟩)).coin))
      E encBool := by
    have hab : ComputableInPolyTime (fun p => p.2.2.aborted) E encBool := by fun_prop
    have hsc : ComputableInPolyTime (fun p => (((blsBankLookupEntry p.2.2.table p.2.1.2).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
        (p.2.2.remaining.headD ⟨false, 0⟩)).coin) E encBool :=
      (by fun_prop : ComputableInPolyTime BLSBankSample.coin encBLSBankSample encBool).comp hsample
    exact ComputableInPolyTime.bool_or' hab
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_not.comp hop) hsc)
  have hrem' : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState => p.2.2.remaining.tail)
      E (encList encBLSBankSample) := by
    have hrem : ComputableInPolyTime (fun p => p.2.2.remaining) E (encList encBLSBankSample) := by
      fun_prop
    exact (ComputableInPolyTime.listTail encBLSBankSample).comp hrem
  have hstate' : ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        (⟨if (blsBankLookupEntry p.2.2.table p.2.1.2).isSome then p.2.2.table
          else ⟨p.2.1.2,
            (((blsBankLookupEntry p.2.2.table p.2.1.2).map
              fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
              (p.2.2.remaining.headD ⟨false, 0⟩)).coin,
            (((blsBankLookupEntry p.2.2.table p.2.1.2).map
              fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
              (p.2.2.remaining.headD ⟨false, 0⟩)).exponent⟩ :: p.2.2.table,
          p.2.2.aborted || (!p.2.1.1 &&
            (((blsBankLookupEntry p.2.2.table p.2.1.2).map
              fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
              (p.2.2.remaining.headD ⟨false, 0⟩)).coin),
          p.2.2.remaining.tail⟩ : BLSBankState))
      E encBLSBankState :=
    (encBLSBankState_mk_polyTime htable' haborted' hrem').of_enc_eq fun _ => rfl
  have hd : ComputableInPolyTime (fun p => p.1.groupParameters) E P.G₀.encDesc := by fun_prop
  have hu : ComputableInPolyTime (fun p => p.1.leftZeroWord) E encBits := by fun_prop
  have hv : ComputableInPolyTime (fun p => p.1.rightZeroWord) E encBits := by fun_prop
  have hreply := (computableInPolyTime_blsBankReplyWord P).comp
    (hd.prod (hu.prod (hv.prod (hop.prod hsample))))
  exact (hreply.prod hstate').of_enc_eq fun p => rfl

private theorem computableInPolyTime_blsBankWordFinish (P : DecodablePairingGroupFamily) :
    ComputableInPolyTime
      (fun p : BLSBankCaller P.toPairingGroupFamily × (List Bool × List Bool) × BLSBankState =>
        blsBankWordFinish P p.1 p.2.1 p.2.2)
      (encPair (encBLSBankCaller P.toPairingGroupFamily)
        (encPair (encPair encBits encBits) encBLSBankState))
      encBits := by
  let E := encPair (encBLSBankCaller P.toPairingGroupFamily)
    (encPair (encPair encBits encBits) encBLSBankState)
  have hd : ComputableInPolyTime (fun p : _ => p.1.groupParameters) E P.G₀.encDesc := by fun_prop
  have hu : ComputableInPolyTime (fun p : _ => p.1.leftZeroWord) E encBits := by fun_prop
  have hmsg : ComputableInPolyTime (fun p : _ => p.2.1.1) E encBits := by fun_prop
  have hsig : ComputableInPolyTime (fun p : _ => p.2.1.2) E encBits := by fun_prop
  have htab : ComputableInPolyTime (fun p : _ => p.2.2.table) E (encList encBLSBankEntry) := by
    fun_prop
  have hrem : ComputableInPolyTime (fun p : _ => p.2.2.remaining) E (encList encBLSBankSample) := by
    fun_prop
  have hab : ComputableInPolyTime (fun p : _ => p.2.2.aborted) E encBool := by fun_prop
  have hfound : ComputableInPolyTime
      (fun p : _ => blsBankLookupEntry p.2.2.table p.2.1.1) E (encOption encBLSBankEntry) := by
    dsimp only [blsBankLookupEntry]
    refine ComputableInPolyTime.findWith
      (test := fun q : List Bool × BLSBankEntry => q.1 == q.2.query) ?_ hmsg htab
    have h1 : ComputableInPolyTime (fun x : List Bool × BLSBankEntry => x.1)
        (encPair encBits encBLSBankEntry) encBits := by fun_prop
    have h2 : ComputableInPolyTime (fun x : List Bool × BLSBankEntry => x.2.query)
        (encPair encBits encBLSBankEntry) encBits := by fun_prop
    exact h1.beq h2
  have hsampleOpt : ComputableInPolyTime
      (fun p : _ => (blsBankLookupEntry p.2.2.table p.2.1.1).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample))
      E (encOption encBLSBankSample) := by
    refine ComputableInPolyTime.optionMapWithInput hfound ?_
    have hc : ComputableInPolyTime (fun x : _ × BLSBankEntry => x.2.coin)
        (encPair E encBLSBankEntry) encBool := by fun_prop
    have hr : ComputableInPolyTime (fun x : _ × BLSBankEntry => x.2.exponent)
        (encPair E encBLSBankEntry) encNat := by fun_prop
    exact (encBLSBankSample_mk_polyTime hc hr).of_enc_eq fun _ => rfl
  have hdefault : ComputableInPolyTime
      (fun p : _ => p.2.2.remaining.headD ⟨false, 0⟩) E encBLSBankSample :=
    (ComputableInPolyTime.headD (encA := encBLSBankSample) ⟨false, 0⟩).comp hrem
  have hsample := ComputableInPolyTime.optionGetDWithInput hsampleOpt hdefault
  have hcoin : ComputableInPolyTime
      (fun p : _ => (((blsBankLookupEntry p.2.2.table p.2.1.1).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
        (p.2.2.remaining.headD ⟨false, 0⟩)).coin) E encBool :=
    (by fun_prop : ComputableInPolyTime BLSBankSample.coin encBLSBankSample encBool).comp hsample
  have hexp : ComputableInPolyTime
      (fun p : _ => (((blsBankLookupEntry p.2.2.table p.2.1.1).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
        (p.2.2.remaining.headD ⟨false, 0⟩)).exponent) E encNat :=
    (by fun_prop : ComputableInPolyTime BLSBankSample.exponent encBLSBankSample encNat).comp
      hsample
  have hzero : ComputableInPolyTime (fun p : _ => P.G₀.encode p.1.groupParameters 0) E encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd
  have hq : ComputableInPolyTime (fun p : _ => P.G₀.order p.1.groupParameters) E encNat :=
    P.G₀.computableInPolyTime_order.comp hd
  have hneg : ComputableInPolyTime
      (fun p : _ => P.G₀.order p.1.groupParameters -
        (((blsBankLookupEntry p.2.2.table p.2.1.1).map
          fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD
          (p.2.2.remaining.headD ⟨false, 0⟩)).exponent % P.G₀.order p.1.groupParameters)
      E encNat :=
    hq.binary_sub' (hexp.binary_mod' hq)
  have hisElem : ComputableInPolyTime (fun p : _ => P.isElem₀ (p.1.groupParameters, p.2.1.2))
      E encBool :=
    P.computableInPolyTime_isElem₀_app hd hsig
  have hsigWord : ComputableInPolyTime
      (fun p : _ =>
        if P.isElem₀ (p.1.groupParameters, p.2.1.2) then p.2.1.2
        else P.G₀.encode p.1.groupParameters 0)
      E encBits :=
    hisElem.ite hsig hzero
  have hadd : ComputableInPolyTime
      (fun p : _ => P.G₀.add (p.1.groupParameters,
        if P.isElem₀ (p.1.groupParameters, p.2.1.2) then p.2.1.2
        else P.G₀.encode p.1.groupParameters 0,
        P.G₀.smul (p.1.groupParameters, _, p.1.leftZeroWord)))
      E encBits :=
    P.G₀.computableInPolyTime_add.comp
      (hd.prod (hsigWord.prod (P.G₀.computableInPolyTime_smul.comp (hd.prod (hneg.prod hu)))))
  exact (hab.ite hzero (hcoin.ite hadd hzero)).of_enc_eq fun _ => rfl

private theorem length_encList_tail_le {α : Type} (enc : α ↪ List Bool) (l : List α) :
    (encList enc l.tail).length ≤ (encList enc l).length := by
  cases l with
  | nil => exact le_rfl
  | cons hd tl =>
    simp only [List.tail_cons, encList_cons, List.length_append]
    exact Nat.le_add_left _ _

private theorem isPPTOn_blsBankReplay (P : PairingGroupFamily)
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) :
    IsPPTOn (encBLSBankCaller P) (encPair (encPair encBits encBits) encBLSBankState)
      (blsBankReplay P machine c e keyC keyD) := by
  unfold blsBankReplay
  have hreplay :
      IsOraclePPTOn encReplayInput (encPair encBits encBits)
        (savedWordReplay machine (fun op word => ProbOracleComp.query (op, word))
          c e keyC keyD) :=
    isOraclePPTOn_savedWordReplay machine c e keyC keyD
  obtain ⟨cR, dR, hlenR⟩ := (computableInPolyTime_blsBankReplyWord P).polyBounded_length.exists_le
  let bankMax (caller : BLSBankCaller P) : ℕ :=
    (encList encBLSBankSample caller.bank).length + (encBLSBankSample ⟨false, 0⟩).length
  let argLen (caller : BLSBankCaller P) : ℕ :=
    2 * (P.G₀.encDesc caller.groupParameters).length + 2 * caller.leftZeroWord.length +
      2 * caller.rightZeroWord.length + bankMax caller + 64
  let resources (caller : BLSBankCaller P) (req : List Bool) : ℕ :=
    max (cR * (argLen caller + 1) ^ dR) (8 * req.length + 4 * bankMax caller + 64)
  let invariant (caller : BLSBankCaller P) (st : BLSBankState) : Prop :=
    (∀ entry ∈ st.table, (encBLSBankSample ⟨entry.coin, entry.exponent⟩).length ≤ bankMax caller) ∧
      ∀ s ∈ st.remaining, (encBLSBankSample s).length ≤ bankMax caller
  have hprepare : ComputableInPolyTime
      (fun caller : BLSBankCaller P =>
        (caller.secParam, caller.leftOneWord, caller.forgerCoins))
      (encBLSBankCaller P) encReplayInput := by
    have hs : ComputableInPolyTime BLSBankCaller.secParam (encBLSBankCaller P) encUnary := by
      fun_prop
    have ho : ComputableInPolyTime BLSBankCaller.leftOneWord (encBLSBankCaller P) encBits := by
      fun_prop
    have hf : ComputableInPolyTime BLSBankCaller.forgerCoins (encBLSBankCaller P) encBits := by
      fun_prop
    exact (hs.prod (ho.prod hf)).of_enc_eq fun _ => rfl
  have horacle :
      IsPPTOn (encHandlerCall (encBLSBankCaller P) (encFinEnum Bool) encBLSBankState)
        (encPair encBits encBLSBankState)
        (fun ⟨caller, request, state⟩ => pure (blsBankWordStep P caller request state)) :=
    (computableInPolyTime_blsBankWordStep P).isPPTOn
  have hinitial : ComputableInPolyTime
      (fun caller : BLSBankCaller P => (⟨[], false, caller.bank⟩ : BLSBankState))
      (encBLSBankCaller P) encBLSBankState := by
    have hrem : ComputableInPolyTime BLSBankCaller.bank (encBLSBankCaller P)
        (encList encBLSBankSample) := by fun_prop
    exact (encBLSBankState_mk_polyTime (ComputableInPolyTime.const [])
      (ComputableInPolyTime.const false) hrem).of_enc_eq fun _ => rfl
  have hinit : ∀ caller : BLSBankCaller P, invariant caller ⟨[], false, caller.bank⟩ := by
    intro caller
    refine ⟨fun _ h => (by cases h), fun s hs => ?_⟩
    exact (length_le_encList_of_mem encBLSBankSample hs).trans (Nat.le_add_right _ _)
  have hresources : ComputableInPolyTime
      (fun pair : BLSBankCaller P × List Bool => resources pair.1 pair.2)
      (encPair (encBLSBankCaller P) encBits) encUnary := by
    dsimp only [resources]
    have hcaller1 : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => p.1)
        (encPair (encBLSBankCaller P) encBits) (encBLSBankCaller P) := by fun_prop
    have hreq : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => p.2)
        (encPair (encBLSBankCaller P) encBits) encBits := by fun_prop
    have hdl : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => (P.G₀.encDesc p.1.groupParameters).length)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.encoding_length P.G₀.encDesc |>.comp
        ((by fun_prop : ComputableInPolyTime BLSBankCaller.groupParameters
          (encBLSBankCaller P) P.G₀.encDesc).comp hcaller1)
    have hbl : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool =>
          (encList encBLSBankSample p.1.bank).length)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.encoding_length (encList encBLSBankSample) |>.comp
        ((by fun_prop : ComputableInPolyTime BLSBankCaller.bank
          (encBLSBankCaller P) (encList encBLSBankSample)).comp hcaller1)
    have hbankMax : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => bankMax p.1)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.unary_add.comp
        (hbl.prod (ComputableInPolyTime.const (encBLSBankSample ⟨false, 0⟩).length))
    have hlenL : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => p.1.leftZeroWord.length)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.length_bits.comp
        ((by fun_prop : ComputableInPolyTime BLSBankCaller.leftZeroWord
          (encBLSBankCaller P) encBits).comp hcaller1)
    have hlenR : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => p.1.rightZeroWord.length)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.length_bits.comp
        ((by fun_prop : ComputableInPolyTime BLSBankCaller.rightZeroWord
          (encBLSBankCaller P) encBits).comp hcaller1)
    have hlenReq : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => p.2.length)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.length_bits.comp hreq
    have hargLen : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => argLen p.1)
        (encPair (encBLSBankCaller P) encBits) encUnary := by
      dsimp only [argLen]
      have hdl2 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hdl)
      have hl2 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hlenL)
      have hr2 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hlenR)
      have h1 := ComputableInPolyTime.unary_add.comp (hdl2.prod hl2)
      have h2 := ComputableInPolyTime.unary_add.comp (h1.prod hr2)
      have h3 := ComputableInPolyTime.unary_add.comp (h2.prod hbankMax)
      exact ComputableInPolyTime.unary_add.comp (h3.prod (ComputableInPolyTime.const 64))
    have hleft : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => cR * (argLen p.1 + 1) ^ dR)
        (encPair (encBLSBankCaller P) encBits) encUnary :=
      ComputableInPolyTime.unary_mul.comp
        ((ComputableInPolyTime.const cR).prod
          ((ComputableInPolyTime.unary_pow dR).comp
            (ComputableInPolyTime.unary_add.comp (hargLen.prod (ComputableInPolyTime.const 1)))))
    have hright : ComputableInPolyTime
        (fun p : BLSBankCaller P × List Bool => 8 * p.2.length + 4 * bankMax p.1 + 64)
        (encPair (encBLSBankCaller P) encBits) encUnary := by
      have h1 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 8).prod hlenReq)
      have h2 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 4).prod hbankMax)
      exact ComputableInPolyTime.unary_add.comp
        ((ComputableInPolyTime.unary_add.comp (h1.prod h2)).prod (ComputableInPolyTime.const 64))
    exact ComputableInPolyTime.unary_max.comp (hleft.prod hright)
  refine IsOraclePPTOn.isPPTOn_runState hreplay hprepare horacle hinitial invariant hinit
    hresources ?_
  intro caller request state hinv result hres
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hres
  subst hres
  dsimp only [blsBankWordStep]
  set found := blsBankLookupEntry state.table request.2
  set sample : BLSBankSample :=
    (found.map fun e => ⟨e.coin, e.exponent⟩).getD (state.remaining.headD ⟨false, 0⟩)
  have hsampleLen : (encBLSBankSample sample).length ≤ bankMax caller := by
    cases hf : found with
    | some entry =>
      have hmem : entry ∈ state.table := List.mem_of_find?_eq_some hf
      have he := hinv.1 entry hmem
      simpa only [sample, hf, Option.map_some, Option.getD_some] using he
    | none =>
      simp only [sample, hf, Option.map_none, Option.getD_none]
      cases hrem : state.remaining with
      | nil => exact Nat.le_add_left _ _
      | cons hd tl => exact hinv.2 hd (hrem ▸ List.mem_cons_self)
  have hinv' :
      invariant caller
        ⟨if found.isSome then state.table
          else ⟨request.2, sample.coin, sample.exponent⟩ :: state.table,
          state.aborted || (!request.1 && sample.coin), state.remaining.tail⟩ := by
    refine ⟨fun entry hentry => ?_, fun s hs => ?_⟩
    · cases hf : found with
      | some _ =>
        simp only [hf, Option.isSome_some, ↓reduceIte] at hentry
        exact hinv.1 entry hentry
      | none =>
        simp only [hf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          List.mem_cons] at hentry
        rcases hentry with rfl | hmem
        · exact hsampleLen
        · exact hinv.1 entry hmem
    · cases hrem : state.remaining with
      | nil =>
        rw [hrem] at hs
        cases hs
      | cons hd tl =>
        rw [hrem, List.tail_cons] at hs
        exact hinv.2 s (hrem ▸ List.mem_cons_of_mem _ hs)
  have hreplyLen :
      (blsBankReplyWord P caller.groupParameters caller.leftZeroWord caller.rightZeroWord
        request.1 sample).length ≤ resources caller request.2 := by
    refine le_trans (hlenR (caller.groupParameters, caller.leftZeroWord, caller.rightZeroWord,
      request.1, sample)) ?_
    refine le_trans ?_ (le_max_left _ _)
    refine Nat.mul_le_mul_left cR (Nat.pow_le_pow_left ?_ dR)
    have harg :
        (encPair P.G₀.encDesc
          (encPair encBits (encPair encBits (encPair encBool encBLSBankSample)))
          (caller.groupParameters, caller.leftZeroWord, caller.rightZeroWord, request.1,
            sample)).length ≤ argLen caller := by
      have hbool : (encBool request.1).length = 1 := by
        cases request.1 <;> simp [encBool_apply]
      dsimp only [argLen]
      enc_len
    omega
  have hstateLen :
      (encBLSBankState
        ⟨if found.isSome then state.table
          else ⟨request.2, sample.coin, sample.exponent⟩ :: state.table,
          state.aborted || (!request.1 && sample.coin), state.remaining.tail⟩).length ≤
        (encBLSBankState state).length + resources caller request.2 := by
    have htail := length_encList_tail_le encBLSBankSample state.remaining
    have habEq : (encBool (state.aborted || (!request.1 && sample.coin))).length =
        (encBool state.aborted).length := by
      cases state.aborted <;> cases request.1 <;> cases sample.coin <;> simp [encBool_apply]
    cases hf : found with
    | some _ =>
      simp only [Option.isSome_some, ↓reduceIte]
      have hs0 :
          (encBLSBankState ⟨state.table, state.aborted || (!request.1 && sample.coin),
            state.remaining.tail⟩).length ≤ (encBLSBankState state).length := by
        enc_len [encBLSBankState_apply]
      exact hs0.trans (Nat.le_add_right _ _)
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have hEntry :
          (encBLSBankEntry ⟨request.2, sample.coin, sample.exponent⟩).length ≤
            2 * request.2.length + bankMax caller + 8 := by
        have hsmp := hsampleLen
        have hboolS : (encBool sample.coin).length = 1 := by
          cases sample.coin <;> simp [encBool_apply]
        simp only [encBLSBankSample_apply, length_encPair, hboolS] at hsmp
        simp only [encBLSBankEntry_apply, encBLSBankEntryFields, length_encPair, encBits_apply,
          hboolS]
        omega
      have hs1 :
          (encBLSBankState ⟨⟨request.2, sample.coin, sample.exponent⟩ :: state.table,
            state.aborted || (!request.1 && sample.coin), state.remaining.tail⟩).length ≤
            (encBLSBankState state).length + (8 * request.2.length + 4 * bankMax caller + 64) := by
        enc_len [encBLSBankState_apply]
      exact hs1.trans (Nat.add_le_add_left (le_max_right _ _) _)
  exact ⟨hinv', hreplyLen, hstateLen⟩

private def blsBankAdversaryCaller (P : PairingGroupFamily)
    (p : ((P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool) × List ℕ) : BLSBankCaller P :=
  ⟨p.1.1.1.secParam, p.1.1.1.groupParameters,
    P.G₀.encode p.1.1.1.groupParameters p.1.1.1.leftZero,
    P.G₁.encode p.1.1.1.groupParameters p.1.1.1.leftOne,
    P.G₀.encode p.1.1.1.groupParameters p.1.1.1.rightZero,
    p.1.1.2, (p.1.2.zip p.2).map fun q => ⟨q.1, q.2⟩⟩

private theorem computableInPolyTime_savedCoinBudget (F : PrimeOrderGroupFamily) (C : F.Companion)
    (c e keyC keyD : ℕ) :
    ComputableInPolyTime (fun x : F.CoCDHInput C => savedCoinBudget c e keyC keyD x.secParam)
      (F.encCoCDHInput C) encUnary := by
  have hid0 : ComputableInPolyTime id (F.encCoCDHInput C) (F.encCoCDHInput C) :=
    ComputableInPolyTime.id'
  have hn0 : ComputableInPolyTime (fun x : F.CoCDHInput C => x.secParam)
      (F.encCoCDHInput C) encUnary :=
    F.encCoCDHInput_secParam_polyTime C hid0
  dsimp only [savedCoinBudget]
  have h1 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hn0)
  have h2 := ComputableInPolyTime.unary_add.comp (h1.prod (ComputableInPolyTime.const 2))
  have h3 := ComputableInPolyTime.unary_mul.comp
    ((ComputableInPolyTime.const keyC).prod
      ((ComputableInPolyTime.unary_pow keyD).comp
        (ComputableInPolyTime.unary_add.comp (hn0.prod (ComputableInPolyTime.const 1)))))
  exact ComputableInPolyTime.unary_mul.comp
    ((ComputableInPolyTime.const c).prod
      ((ComputableInPolyTime.unary_pow e).comp (ComputableInPolyTime.unary_add.comp (h2.prod h3))))

private theorem computableInPolyTime_blsBankAdversaryCaller (P : PairingGroupFamily) :
    ComputableInPolyTime
      (blsBankAdversaryCaller P)
      (encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
        (encList encNat))
      (encBLSBankCaller P) := by
  let E3 :=
    encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)) (encList encNat)
  have hfst3 : ComputableInPolyTime
      (fun p : ((P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool) × List ℕ => p.1)
      E3 (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)) :=
    ComputableInPolyTime.fst _ _
  have hfst2 : ComputableInPolyTime
      (fun p : (P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool => p.1)
      (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
      (encPair (P.G₀.encCoCDHInput P.G₁) encBits) :=
    ComputableInPolyTime.fst _ _
  have hx : ComputableInPolyTime
      (fun p : ((P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool) × List ℕ => p.1.1.1)
      E3 (P.G₀.encCoCDHInput P.G₁) :=
    (ComputableInPolyTime.fst _ _).comp (hfst2.comp hfst3)
  have hn : ComputableInPolyTime (fun p => p.1.1.1.secParam) E3 encUnary :=
    P.G₀.encCoCDHInput_secParam_polyTime P.G₁ hx
  have hd : ComputableInPolyTime (fun p => p.1.1.1.groupParameters) E3 P.G₀.encDesc :=
    P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ hx
  have hlz : ComputableInPolyTime
      (fun p => P.G₀.encode p.1.1.1.groupParameters p.1.1.1.leftZero) E3 encBits :=
    P.G₀.encCoCDHInput_leftZero_polyTime P.G₁ hx
  have hlo : ComputableInPolyTime
      (fun p => P.G₁.encode p.1.1.1.groupParameters p.1.1.1.leftOne) E3 encBits :=
    P.G₀.encCoCDHInput_leftOne_polyTime P.G₁ hx
  have hrz : ComputableInPolyTime
      (fun p => P.G₀.encode p.1.1.1.groupParameters p.1.1.1.rightZero) E3 encBits :=
    P.G₀.encCoCDHInput_rightZero_polyTime P.G₁ hx
  have hs : ComputableInPolyTime (fun p => p.1.1.2) E3 encBits :=
    (ComputableInPolyTime.snd _ _).comp (hfst2.comp hfst3)
  have hcs : ComputableInPolyTime (fun p => p.1.2) E3 (encList encBool) :=
    (ComputableInPolyTime.snd _ _).comp hfst3
  have hrhos : ComputableInPolyTime (fun p => p.2) E3 (encList encNat) :=
    ComputableInPolyTime.snd _ _
  have hzip : ComputableInPolyTime (fun p => p.1.2.zip p.2) E3 (encList (encPair encBool encNat)) :=
    (ComputableInPolyTime.zip encBool encNat).comp (hcs.prod hrhos)
  have hbank : ComputableInPolyTime
      (fun p => (p.1.2.zip p.2).map fun q => (⟨q.1, q.2⟩ : BLSBankSample))
      E3 (encList encBLSBankSample) := by
    refine (ComputableInPolyTime.map (encA := encPair encBool encNat)
      (encB := encBLSBankSample) ?_).comp hzip
    have hb1 : ComputableInPolyTime (fun q : Bool × ℕ => q.1) (encPair encBool encNat) encBool :=
      ComputableInPolyTime.fst encBool encNat
    have hb2 : ComputableInPolyTime (fun q : Bool × ℕ => q.2) (encPair encBool encNat) encNat :=
      ComputableInPolyTime.snd encBool encNat
    exact (encBLSBankSample_mk_polyTime hb1 hb2).of_enc_eq fun _ => rfl
  exact (encBLSBankCaller_mk_polyTime P hn hd hlz hlo hrz hs hbank).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_blsBankAdversaryFinish (P : DecodablePairingGroupFamily) :
    ComputableInPolyTime
      (fun q : (((P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool) × List ℕ) ×
          ((List Bool × List Bool) × BLSBankState) =>
        let caller := blsBankAdversaryCaller P.toPairingGroupFamily q.1
        let outWord := blsBankWordFinish P caller q.2.1 q.2.2
        if P.isElem₀ (caller.groupParameters, outWord) then outWord
        else P.G₀.encode caller.groupParameters 0)
      (encPair
        (encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
          (encList encNat))
        (encPair (encPair encBits encBits) encBLSBankState))
      encBits := by
  let E3 :=
    encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)) (encList encNat)
  let E4 := encPair E3 (encPair (encPair encBits encBits) encBLSBankState)
  have hc4 : ComputableInPolyTime (fun q => blsBankAdversaryCaller P.toPairingGroupFamily q.1)
      E4 (encBLSBankCaller P.toPairingGroupFamily) :=
    (computableInPolyTime_blsBankAdversaryCaller P.toPairingGroupFamily).comp
      (ComputableInPolyTime.fst _ _)
  have hr4 : ComputableInPolyTime
      (fun q : (((P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool) × List ℕ) ×
          ((List Bool × List Bool) × BLSBankState) => q.2)
      E4 (encPair (encPair encBits encBits) encBLSBankState) :=
    ComputableInPolyTime.snd _ _
  have hout : ComputableInPolyTime
      (fun q => blsBankWordFinish P (blsBankAdversaryCaller P.toPairingGroupFamily q.1) q.2.1 q.2.2)
      E4 encBits :=
    (computableInPolyTime_blsBankWordFinish P).comp (hc4.prod hr4)
  have hx : ComputableInPolyTime (fun q => q.1.1.1.1) E4 (P.G₀.encCoCDHInput P.G₁) :=
    (ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.fst _ _).comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
  have hd4 : ComputableInPolyTime (fun q => q.1.1.1.1.groupParameters) E4 P.G₀.encDesc :=
    P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ hx
  have his : ComputableInPolyTime
      (fun q => P.isElem₀ (q.1.1.1.1.groupParameters,
        blsBankWordFinish P (blsBankAdversaryCaller P.toPairingGroupFamily q.1) q.2.1 q.2.2))
      E4 encBool :=
    P.computableInPolyTime_isElem₀_app hd4 hout
  have hz : ComputableInPolyTime (fun q => P.G₀.encode q.1.1.1.1.groupParameters 0) E4 encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd4
  exact (his.ite hout hz).of_enc_eq fun _ => rfl

/-- **The explicit banked co-CDH reduction is uniform strict PPT** (`[BonehShoup2023]`,
Theorem 15.1, pp. 628–629). -/
theorem isPPT_blsBankedCoCDHAdversary (P : DecodablePairingGroupFamily)
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) :
    (blsBankedCoCDHAdversary P machine c e keyC keyD).IsPPT := by
  dsimp only [PrimeOrderGroupFamily.CoCDHAdversary.IsPPT]
  have hid0 : ComputableInPolyTime id (P.G₀.encCoCDHInput P.G₁) (P.G₀.encCoCDHInput P.G₁) :=
    ComputableInPolyTime.id'
  have hn0 : ComputableInPolyTime (fun x : P.G₀.CoCDHInput P.G₁ => x.secParam)
      (P.G₀.encCoCDHInput P.G₁) encUnary :=
    P.G₀.encCoCDHInput_secParam_polyTime P.G₁ hid0
  have hd0 : ComputableInPolyTime (fun x : P.G₀.CoCDHInput P.G₁ => x.groupParameters)
      (P.G₀.encCoCDHInput P.G₁) P.G₀.encDesc :=
    P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ hid0
  have hbud0 : ComputableInPolyTime
      (fun x : P.G₀.CoCDHInput P.G₁ => savedCoinBudget c e keyC keyD x.secParam)
      (P.G₀.encCoCDHInput P.G₁) encUnary :=
    computableInPolyTime_savedCoinBudget P.G₀ P.G₁ c e keyC keyD
  have hs0 : IsPPTOn (P.G₀.encCoCDHInput P.G₁) encBits
      (fun x : P.G₀.CoCDHInput P.G₁ =>
        BitString.sampleList (savedCoinBudget c e keyC keyD x.secParam)) :=
    hbud0.sampleList
  have hbud1 : ComputableInPolyTime
      (fun p : P.G₀.CoCDHInput P.G₁ × List Bool =>
        savedCoinBudget c e keyC keyD p.1.secParam)
      (encPair (P.G₀.encCoCDHInput P.G₁) encBits) encUnary :=
    hbud0.comp (ComputableInPolyTime.fst (P.G₀.encCoCDHInput P.G₁) encBits)
  have hK1 : ComputableInPolyTime
      (fun p : P.G₀.CoCDHInput P.G₁ × List Bool =>
        savedCoinBudget c e keyC keyD p.1.secParam +
          savedCoinBudget c e keyC keyD p.1.secParam + 1)
      (encPair (P.G₀.encCoCDHInput P.G₁) encBits) encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_add.comp (hbud1.prod hbud1)).prod (ComputableInPolyTime.const 1))
  have hcoin1 : IsPPTOn (encPair (P.G₀.encCoCDHInput P.G₁) encBits) encBool
      (fun p : P.G₀.CoCDHInput P.G₁ × List Bool =>
        ProbComp.sampleDyadicCoin (savedCoinBudget c e keyC keyD p.1.secParam) 1) :=
    isPPTOn_sampleDyadicCoin hbud1 (ComputableInPolyTime.const 1)
  have hcs1 : IsPPTOn (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)
      (fun p : P.G₀.CoCDHInput P.G₁ × List Bool =>
        OracleComp.replicate
          (savedCoinBudget c e keyC keyD p.1.secParam +
            savedCoinBudget c e keyC keyD p.1.secParam + 1)
          (ProbComp.sampleDyadicCoin (savedCoinBudget c e keyC keyD p.1.secParam) 1)) :=
    hcoin1.replicate hK1
  have hfst2 : ComputableInPolyTime
      (fun p : (P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool => p.1)
      (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
      (encPair (P.G₀.encCoCDHInput P.G₁) encBits) :=
    ComputableInPolyTime.fst _ _
  have hx2 : ComputableInPolyTime
      (fun p : (P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool => p.1.1)
      (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
      (P.G₀.encCoCDHInput P.G₁) :=
    (ComputableInPolyTime.fst _ _).comp hfst2
  have hexp2 : IsPPTOn
      (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)) encNat
      (fun p : (P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool =>
        P.G₀.sampleExp p.1.1.secParam p.1.1.groupParameters) :=
    P.G₀.isPPTOn_sampleExp (hn0.comp hx2) (hd0.comp hx2)
  have hrhos2 : IsPPTOn
      (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool)) (encList encNat)
      (fun p : (P.G₀.CoCDHInput P.G₁ × List Bool) × List Bool =>
        OracleComp.replicate
          (savedCoinBudget c e keyC keyD p.1.1.secParam +
            savedCoinBudget c e keyC keyD p.1.1.secParam + 1)
          (P.G₀.sampleExp p.1.1.secParam p.1.1.groupParameters)) :=
    hexp2.replicate (hK1.comp hfst2)
  have hcaller := computableInPolyTime_blsBankAdversaryCaller P.toPairingGroupFamily
  have hrun := (isPPTOn_blsBankReplay P.toPairingGroupFamily machine c e keyC keyD).preprocess
    hcaller
  have hfin := computableInPolyTime_blsBankAdversaryFinish P
  have hstep4 := hrun.keep_input.bind hfin.isPPTOn
  have hstep3 := hrhos2.keep_input.bind hstep4
  have hstep2 := hcs1.keep_input.bind hstep3
  have hcomp := hs0.keep_input.bind hstep2
  refine hcomp.congr fun x => ?_
  dsimp only [blsBankedCoCDHAdversary, blsBankAdversaryCaller]
  simp only [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
    PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun cs _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun rhos _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun res _ => ?_
  rw [PMF.pure_map]
  exact congrArg PMF.pure
    (P.toDecodableG₀.encode_decode_getD x.groupParameters _
      (0 : P.G₀.Carrier x.groupParameters)).symm

/-! ### Bridging native word forgers to typed BLS and banked co-CDH -/

private def blsDecodedForger (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (P.G₀.Carrier d)) :
    Forger (P.G₁.Carrier d) (List Bool) (P.G₀.Carrier d) (List Bool) (P.G₀.Carrier d) where
  Coins := A.Coins
  coins := A.coins
  forge u s :=
    Prod.map id (fun sigWord => (P.decode₀ d sigWord).getD 0) <$>
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun msg => P.G₀.encode d <$>
            OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
              (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
          (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
              (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
        (A.forge (P.G₁.encode d u) s)

private theorem callBounded_blsDecodedForger (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    {A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (P.G₀.Carrier d)} {Qs Qro : ℕ}
    (hA : A.CallBounded Qs Qro) : (blsDecodedForger P d A).CallBounded Qs Qro := by
  intro u s
  let route : (q : List Bool ⊕ List Bool) →
      OracleComp (ForgerSpec (List Bool) (List Bool) (P.G₀.Carrier d) (P.G₀.Carrier d))
        (ForgerSpec (List Bool) (List Bool) (List Bool) (P.G₀.Carrier d) q) :=
    OracleComp.sumHandler
      (fun msg => P.G₀.encode d <$> OracleComp.query (Sum.inl msg))
      (fun q => OracleComp.query (Sum.inr q))
  have hroute (cost : List Bool ⊕ List Bool → ℕ) (q : List Bool ⊕ List Bool) :
      OracleComp.IsCostBounded cost (route q) (cost q) := by
    cases q with
    | inl msg =>
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    | inr q => exact OracleComp.IsCostBounded.query _
  constructor
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (OracleComp.IsCostBounded.interpret (hroute signingCost) (hA (P.G₁.encode d u) s).1)
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (OracleComp.IsCostBounded.interpret (hroute hashCost) (hA (P.G₁.encode d u) s).2)

private theorem interpret_handler_blsNative_eq_decoded (P : DecodablePairingGroupFamily)
    (n : ℕ) (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (α : ZMod (P.G₀.order d))
    (prog : OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool) (P.G₀.Carrier d))
      (List Bool × List Bool))
    (state : List (List Bool × P.G₀.Carrier d) × List (List Bool)) :
    (OracleComp.interpret
        (handler (P.blsNativeROMScheme n d) (P.G₁.toFamily.encScalar d α)) prog).run state =
      ((OracleComp.interpret (handler (P.toPairingGroupFamily.blsTypedROMScheme d) α)
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun msg => P.G₀.encode d <$>
              OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
            (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
          prog)).run state) := by
  have hsk : (Turing.MultiTapeTM.ofBits (P.G₁.toFamily.encScalar d α) : ZMod (P.G₀.order d)) =
      α := by
    change ((Turing.MultiTapeTM.ofBits (Turing.MultiTapeTM.encNat α.val) : ℕ) :
      ZMod (P.G₀.order d)) = α
    have hnat : Turing.MultiTapeTM.ofBits (Turing.MultiTapeTM.encNat α.val) = α.val :=
      Turing.MultiTapeTM.Decoder.nat.decode_enc α.val
    rw [hnat, ZMod.natCast_zmod_val]
  induction prog using OracleComp.induction generalizing state with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure]
  | query_bind q cont ih =>
    change (OracleComp.interpret (handler (P.blsNativeROMScheme n d)
      (P.G₁.toFamily.encScalar d α)) (OracleComp.query q >>= cont)).run state =
      (OracleComp.interpret (handler (P.toPairingGroupFamily.blsTypedROMScheme d) α)
        (OracleComp.interpret _ (OracleComp.query q >>= cont))).run state
    cases q with
    | inl m =>
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
        OracleComp.interpret_map, handler, blsNativeROMScheme,
        PairingGroupFamily.blsTypedROMScheme, StateT.run_map, PMF.monad_pure_eq_pure,
        PMF.monad_bind_eq_bind, PMF.bind_const]
      dsimp only [StateT.run, OracleComp.sumHandler_inl]
      simp only [PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def, PMF.bind_bind,
        PMF.pure_bind]
      refine PMF.bind_congr_on_support _ _ _ fun r _ => ?_
      simpa only [StateT.run, blsNativeROMScheme, PairingGroupFamily.blsTypedROMScheme, hsk,
        P.G₀.smul_encode] using ih (P.G₀.encode d (α • r.1)) (r.2, m :: state.2)
    | inr x =>
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind, handler,
        PMF.monad_bind_eq_bind]
      dsimp only [StateT.run, OracleComp.sumHandler_inr]
      simp only [PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
      refine PMF.bind_congr_on_support _ _ _ fun r _ => ?_
      exact ih r.1 (r.2, state.2)

private theorem succProbability_eufCmaGame_blsNativeROMScheme_le
    (P : DecodablePairingGroupFamily) (n : ℕ) (d : P.G₀.Desc) [Fintype (P.G₀.Carrier d)]
    (A : Forger (List Bool) (List Bool) (List Bool) (List Bool) (P.G₀.Carrier d)) :
    (Game.succProbability (eufCmaGame (P.blsNativeROMScheme n d) A) : ℝ) ≤
      (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d)
        (blsDecodedForger P d A)) : ℝ) + (1 : ℝ) / 2 ^ n := by
  let idealScheme : Scheme (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
      (P.G₀.Carrier d) :=
    { P.blsNativeROMScheme n d with keyGen := P.G₁.toFamily.schnorrIdealKeyGen d }
  have hcloseKey :
      CloseTo (P.blsNativeROMScheme n d).keyGen idealScheme.keyGen ((1 : ℝ≥0) / 2 ^ n : ℝ≥0) := by
    simpa only [blsNativeROMScheme, idealScheme] using
      (P.G₁.toFamily.closeTo_schnorrSigKeyGen n d).symm
  have hcloseGame :
      CloseTo (eufCmaGame (P.blsNativeROMScheme n d) A) (eufCmaGame idealScheme A)
        ((1 : ℝ≥0) / 2 ^ n : ℝ≥0) := by
    unfold eufCmaGame
    exact hcloseKey.bind_left _
  have hadv := Game.coe_succProbability_le_add_of_advantage_le
    (NNReal.coe_le_coe.mpr (Game.closeTo_iff_advantage_le.mp hcloseGame))
  have hideal_le :
      Game.succProbability (eufCmaGame idealScheme A) ≤
        Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d)
          (blsDecodedForger P d A)) := by
    apply Game.succProbability_mono
    unfold eufCmaGame
    rw [show idealScheme.keyGen = P.G₁.toFamily.schnorrIdealKeyGen d from rfl]
    dsimp only [PrimeOrderGroupFamily.schnorrIdealKeyGen,
      PairingGroupFamily.blsTypedROMScheme, blsDecodedForger,
      PrimeOrderGroupFamily.Companion.toFamily]
    simp only [PMF.monad_bind_eq_bind, PMF.bind_map]
    refine PMF.bind_apply_mono_on_support _ _ fun α _ => ?_
    refine PMF.bind_apply_mono_on_support _ _ fun s _ => ?_
    dsimp only
    have hhand : handler idealScheme = handler (P.blsNativeROMScheme n d) := rfl
    rw [hhand, interpret_handler_blsNative_eq_decoded]
    simp only [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map, PMF.bind_map]
    refine PMF.bind_apply_mono_on_support _ _ fun forged _ => ?_
    dsimp only [idealScheme, blsNativeROMScheme, PairingGroupFamily.blsTypedROMScheme]
    simp only [OracleComp.interpret_map, OracleComp.interpret_query, StateT.run_map,
      PMF.monad_map_eq_map, PMF.bind_map]
    refine PMF.bind_apply_mono_on_support _ _ fun r _ => ?_
    dsimp only [Function.comp_def, Prod.map, id_eq]
    simp only [PMF.monad_pure_eq_pure, PMF.pure_apply]
    split_ifs with hwin1 hwin2 hwin2'
    · exact le_rfl
    · exfalso
      have hwin' := hwin1.symm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin'
      obtain ⟨⟨helem, hpair⟩, hfresh⟩ := hwin'
      obtain ⟨σ', hdec, hσ⟩ := P.toDecodableG₀.exists_decode_eq_some_of_isElem helem
      let σ : P.G₀.Carrier d := σ'
      have hget : (P.decode₀ d forged.1.2).getD (0 : P.G₀.Carrier d) = σ := by
        rw [show P.decode₀ d forged.1.2 = some σ from hdec]
        rfl
      have hσ' : P.G₀.encode d σ = forged.1.2 := hσ
      rw [← hσ', P.pairEncoded_encode, P.pairEncoded_encode,
        (P.GT.encode_injective d).eq_iff] at hpair
      have hbeq :
          @List.contains (List Bool) List.instBEq forged.2.2 forged.1.1 =
            @List.contains (List Bool) instBEqOfDecidableEq forged.2.2 forged.1.1 := by
        apply Bool.eq_iff_iff.mpr
        simp
      have hfresh' : @List.contains (List Bool) instBEqOfDecidableEq forged.2.2 forged.1.1 =
          false := by
        simpa only [hbeq, Bool.not_eq_true'] using hfresh
      have hrhs :
          (decide (P.pair d r.1 (α • P.G₁.generator d) =
              P.pair d ((P.decode₀ d forged.1.2).getD 0) (P.G₁.generator d)) &&
            !@List.contains (List Bool) instBEqOfDecidableEq forged.2.2 forged.1.1) = true := by
        simp only [hget, hpair, hfresh', Bool.not_false, decide_true, Bool.true_and]
      exact hwin2 hrhs.symm
    · exact zero_le
    · exact zero_le
  have hreal : (Game.succProbability (eufCmaGame idealScheme A) : ℝ) ≤
      (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d)
        (blsDecodedForger P d A)) : ℝ) := by
    exact_mod_cast hideal_le
  calc
    (Game.succProbability (eufCmaGame (P.blsNativeROMScheme n d) A) : ℝ)
        ≤ (Game.succProbability (eufCmaGame idealScheme A) : ℝ) +
            ((1 : ℝ≥0) / 2 ^ n : ℝ) := hadv
    _ ≤ (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d)
          (blsDecodedForger P d A)) : ℝ) + (1 : ℝ) / 2 ^ n := by
        push_cast
        exact add_le_add hreal le_rfl

private theorem blsBankLookupEntry_map_eq (q : ℕ) (key : List Bool)
    (tabW : List BLSBankEntry) (tabT : List (List Bool × ((Bool × ZMod q) × ℕ)))
    (htab : tabW.map (fun e => (e.query, (e.coin, (e.exponent : ZMod q)))) =
      tabT.map (fun e => (e.1, e.2.1))) :
    ((blsBankLookupEntry tabW key).map fun e => (e.coin, (e.exponent : ZMod q))) =
      (tabT.lookup key).map Prod.fst := by
  induction tabW generalizing tabT with
  | nil =>
    cases tabT with
    | nil => rfl
    | cons _ _ => cases htab
  | cons hdW tlW ihW =>
    cases tabT with
    | nil => cases htab
    | cons hdT tlT =>
      simp only [List.map_cons, List.cons.injEq] at htab
      obtain ⟨hhd, htl⟩ := htab
      dsimp only [blsBankLookupEntry]
      rw [List.find?_cons, List.lookup_cons_eq_ite]
      obtain ⟨hqhd, hvalhd⟩ := Prod.mk.inj hhd
      by_cases heq : key = hdW.query
      · simp [heq, hqhd, hvalhd]
      · have hbeq : (key == hdW.query) = false := beq_false_of_ne heq
        have hne' : key ≠ hdT.1 := fun h => heq (h.trans hqhd.symm)
        dsimp only [blsBankLookupEntry] at ihW ⊢
        simpa [hbeq, hne', beq_iff_eq] using ihW tlT htl

private theorem blsWordBankStep_eq_blsBankedReductionStep
    (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    (u₀ : P.G₀.Carrier d) (u₁ : P.G₁.Carrier d) (v₀ : P.G₀.Carrier d)
    (forgerCoins : List Bool) (n : ℕ)
    (samples : List BLSBankSample)
    (prog : OracleComp RawWordSpec (List Bool × List Bool))
    (tabW : List BLSBankEntry) (tabT : List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ)))
    (aborted : Bool) (count : ℕ)
    (htab : tabW.map (fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
      tabT.map (fun e => (e.1, e.2.1))) :
    let caller : BLSBankCaller P.toPairingGroupFamily :=
      ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
    let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
    let samplesT : List (Bool × ZMod (P.G₀.order d)) :=
      samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))
    let wRun := (OracleComp.interpret (blsBankWordHandler P.toPairingGroupFamily caller)
      prog).run ⟨tabW, aborted, samples.drop count⟩
    let tRun := (OracleComp.interpret
      (P.toPairingGroupFamily.blsBankedReductionStep d u₀ v₀ samplesT)
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun msg => P.G₀.encode d <$> OracleComp.query (Sum.inl msg))
          (fun q => OracleComp.query (Sum.inr q)))
        (OracleComp.interpret (fun request => wordQuery digestEnc request.1 request.2)
          prog))).run (tabT, aborted, count)
    wRun.1 = tRun.1 ∧
      wRun.2.aborted = tRun.2.2.1 ∧
      wRun.2.remaining = samples.drop tRun.2.2.2 ∧
      wRun.2.table.map (fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
        tRun.2.1.map (fun e => (e.1, e.2.1)) := by
  induction prog using OracleComp.induction generalizing tabW tabT aborted count with
  | pure a =>
    exact ⟨rfl, rfl, rfl, htab⟩
  | query_bind q cont ih =>
    have hlook :
        ((blsBankLookupEntry tabW q.2).map
          fun e => (e.coin, (e.exponent : ZMod (P.G₀.order d)))) =
          (tabT.lookup q.2).map Prod.fst :=
      blsBankLookupEntry_map_eq (P.G₀.order d) q.2 tabW tabT htab
    have hget :
        (fun s : BLSBankSample => (s.coin, (s.exponent : ZMod (P.G₀.order d))))
          ((samples.drop count).headD ⟨false, 0⟩) =
        (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD count
          (false, 0) := by
      rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop,
        List.getElem?_map]
      cases samples[count]? <;> simp
    have hid : ∀ {α β : Type} (x : α) (f : α → Id β), Bind.bind (m := Id) x f = f x :=
      fun _ _ => rfl
    have hdrop : (samples.drop count).tail = samples.drop (count + 1) := by
      simp only [List.tail_drop]
    rcases q with ⟨op, word⟩
    dsimp only at hlook hget
    let caller : BLSBankCaller P.toPairingGroupFamily :=
      ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
    let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
    let samplesT : List (Bool × ZMod (P.G₀.order d)) :=
      samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))
    change
      (fun (wRun : (List Bool × List Bool) × BLSBankState)
        (tRun : (List Bool × List Bool) ×
          List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ)) × Bool × ℕ) =>
        wRun.1 = tRun.1 ∧
          wRun.2.aborted = tRun.2.2.1 ∧
          wRun.2.remaining = samples.drop tRun.2.2.2 ∧
          wRun.2.table.map (fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
            tRun.2.1.map (fun e => (e.1, e.2.1)))
        ((OracleComp.interpret (blsBankWordHandler P.toPairingGroupFamily caller)
          (OracleComp.query (spec := RawWordSpec) (op, word) >>= cont)).run
          ⟨tabW, aborted, samples.drop count⟩)
        ((OracleComp.interpret
          (P.toPairingGroupFamily.blsBankedReductionStep d u₀ v₀ samplesT)
          (OracleComp.interpret
            (OracleComp.sumHandler
              (fun msg => P.G₀.encode d <$>
                OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                  (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
              (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                  (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
            (OracleComp.interpret (fun request : Bool × List Bool =>
                wordQuery digestEnc request.1 request.2)
              (OracleComp.query (spec := RawWordSpec) (op, word) >>= cont)))).run
          (tabT, aborted, count))
    cases op with
    | false =>
      cases hfl : tabT.lookup word with
      | some entry =>
        rcases entry with ⟨⟨cT, ρT⟩, idxT⟩
        have hflW : ∃ eW, blsBankLookupEntry tabW word = some eW ∧
            (eW.coin, (eW.exponent : ZMod (P.G₀.order d))) = (cT, ρT) := by
          rw [hfl, Option.map_some] at hlook
          cases hfW : blsBankLookupEntry tabW word with
          | none => simp [hfW] at hlook
          | some eW =>
            simp only [hfW, Option.map_some, Option.some.injEq] at hlook
            exact ⟨eW, rfl, hlook⟩
        obtain ⟨eW, heW, hval⟩ := hflW
        obtain ⟨hc, hre⟩ := Prod.mk.inj hval
        have hstepW :
            blsBankWordStep P.toPairingGroupFamily
              ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
              (false, word) ⟨tabW, aborted, samples.drop count⟩ =
              (if eW.coin then P.G₀.encode d 0
                else P.G₀.smul (d, eW.exponent, P.G₀.encode d u₀),
                ⟨tabW, aborted || eW.coin, samples.drop (count + 1)⟩) := by
          dsimp only [blsBankWordStep]
          rw [heW]
          simp only [Option.map_some, Option.getD_some, Option.isSome_some, ↓reduceIte,
            Bool.not_false, Bool.true_and, blsBankReplyWord, Bool.false_eq_true, hdrop]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_map, wordQuery, StateT.run_bind, StateT.run_map]
        dsimp only [caller, digestEnc, samplesT, blsBankWordHandler, StateT.run, Functor.map,
          Id.run]
        rw [hstepW]
        dsimp only [PairingGroupFamily.blsBankedReductionStep]
        rw [hfl, hid, hid]
        by_cases hcoin : cT = true
        · have hcW : eW.coin = true := hc.trans hcoin
          simp only [hcW, hcoin, ↓reduceIte, Bool.or_true]
          exact ih (P.G₀.encode d 0) tabW tabT true (count + 1) htab
        · have hcf : cT = false := Bool.eq_false_iff.mpr hcoin
          have hcW : eW.coin = false := hc.trans hcf
          simp only [hcW, hcf, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
          have hsmul :
              P.G₀.smul (d, eW.exponent, P.G₀.encode d u₀) =
                P.G₀.encode d (ρT • u₀) := by
            rw [P.G₀.smul_encode, hre]
          rw [hsmul]
          exact ih (P.G₀.encode d (ρT • u₀)) tabW tabT aborted (count + 1) htab
      | none =>
        have hflW : blsBankLookupEntry tabW word = none := by
          rw [hfl, Option.map_none] at hlook
          cases hfW : blsBankLookupEntry tabW word with
          | none => rfl
          | some _ => simp [hfW] at hlook
        let valW := (samples.drop count).headD ⟨false, 0⟩
        let valT := (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD count
          (false, 0)
        have hval : (valW.coin, (valW.exponent : ZMod (P.G₀.order d))) = valT := hget
        have hc : valW.coin = valT.1 := congrArg Prod.fst hval
        have hre : (valW.exponent : ZMod (P.G₀.order d)) = valT.2 := congrArg Prod.snd hval
        have hstepW :
            blsBankWordStep P.toPairingGroupFamily
              ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
              (false, word) ⟨tabW, aborted, samples.drop count⟩ =
              (if valW.coin then P.G₀.encode d 0
                else P.G₀.smul (d, valW.exponent, P.G₀.encode d u₀),
                ⟨⟨word, valW.coin, valW.exponent⟩ :: tabW, aborted || valW.coin,
                  samples.drop (count + 1)⟩) := by
          dsimp only [blsBankWordStep]
          rw [hflW]
          simp only [Option.map_none, Option.getD_none, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, Bool.not_false, Bool.true_and, blsBankReplyWord, hdrop]
          rfl
        have htab' :
            ((⟨word, valW.coin, valW.exponent⟩ :: tabW).map
              fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
              ((word, (valT, count)) :: tabT).map fun e => (e.1, e.2.1) := by
          simp only [List.map_cons, htab, hval]
        have hvalT_def :
            (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD count
              (false, 0) = valT := rfl
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_map, wordQuery, StateT.run_bind, StateT.run_map]
        dsimp only [caller, digestEnc, samplesT, blsBankWordHandler, StateT.run, Functor.map,
          Id.run]
        rw [hstepW]
        dsimp only [PairingGroupFamily.blsBankedReductionStep]
        rw [hfl, hid, hid, hvalT_def]
        by_cases hcoin : valT.1 = true
        · have hcW : valW.coin = true := hc.trans hcoin
          simp only [hcW, hcoin, ↓reduceIte, Bool.or_true]
          simp only [hcW] at htab'
          exact ih (P.G₀.encode d 0)
            (⟨word, true, valW.exponent⟩ :: tabW) ((word, (valT, count)) :: tabT) true
            (count + 1) htab'
        · have hcf : valT.1 = false := Bool.eq_false_iff.mpr hcoin
          have hcW : valW.coin = false := hc.trans hcf
          simp only [hcW, hcf, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
          have hsmul :
              P.G₀.smul (d, valW.exponent, P.G₀.encode d u₀) = P.G₀.encode d (valT.2 • u₀) := by
            rw [P.G₀.smul_encode, hre]
          rw [hsmul]
          simp only [hcW] at htab'
          exact ih (P.G₀.encode d (valT.2 • u₀))
            (⟨word, false, valW.exponent⟩ :: tabW) ((word, (valT, count)) :: tabT) aborted
            (count + 1) htab'
    | true =>
      cases hfl : tabT.lookup word with
      | some entry =>
        rcases entry with ⟨sampleT, idxT⟩
        have hflW : ∃ eW, blsBankLookupEntry tabW word = some eW ∧
            (eW.coin, (eW.exponent : ZMod (P.G₀.order d))) = sampleT := by
          rw [hfl, Option.map_some] at hlook
          cases hfW : blsBankLookupEntry tabW word with
          | none => simp [hfW] at hlook
          | some eW =>
            simp only [hfW, Option.map_some, Option.some.injEq] at hlook
            exact ⟨eW, rfl, hlook⟩
        obtain ⟨eW, heW, hval⟩ := hflW
        have hstepW :
            blsBankWordStep P.toPairingGroupFamily
              ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
              (true, word) ⟨tabW, aborted, samples.drop count⟩ =
              (coronSampleWord P.toPairingGroupFamily d (P.G₀.encode d v₀)
                  ⟨eW.coin, eW.exponent⟩,
                ⟨tabW, aborted, samples.drop (count + 1)⟩) := by
          dsimp only [blsBankWordStep]
          rw [heW]
          simp only [Option.map_some, Option.getD_some, Option.isSome_some, ↓reduceIte,
            Bool.not_true, Bool.false_and, Bool.or_false, blsBankReplyWord, hdrop]
        have hcoron :
            coronSampleWord P.toPairingGroupFamily d (P.G₀.encode d v₀) ⟨eW.coin, eW.exponent⟩ =
              P.G₀.encode d (P.toPairingGroupFamily.coronSampleElem d v₀ sampleT) := by
          unfold coronSampleWord PairingGroupFamily.coronSampleElem
          obtain ⟨hc, hre⟩ := Prod.mk.inj hval
          rw [hc]
          cases sampleT.1
          · simp only [Bool.false_eq_true, ↓reduceIte, P.G₀.smul_encode, hre]
          · simp only [↓reduceIte, P.G₀.smul_encode, P.G₀.add_encode, hre]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_map, wordQuery, StateT.run_bind, StateT.run_map]
        dsimp only [caller, digestEnc, samplesT, blsBankWordHandler, StateT.run, Functor.map,
          Id.run]
        rw [hstepW, hcoron]
        dsimp only [PairingGroupFamily.blsBankedReductionStep]
        rw [hfl, hid, hid]
        exact ih (P.G₀.encode d (P.toPairingGroupFamily.coronSampleElem d v₀ sampleT)) tabW tabT
          aborted (count + 1) htab
      | none =>
        have hflW : blsBankLookupEntry tabW word = none := by
          rw [hfl, Option.map_none] at hlook
          cases hfW : blsBankLookupEntry tabW word with
          | none => rfl
          | some _ => simp [hfW] at hlook
        let valW := (samples.drop count).headD ⟨false, 0⟩
        let valT := (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD count
          (false, 0)
        have hval : (valW.coin, (valW.exponent : ZMod (P.G₀.order d))) = valT := hget
        have hstepW :
            blsBankWordStep P.toPairingGroupFamily
              ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
              (true, word) ⟨tabW, aborted, samples.drop count⟩ =
              (coronSampleWord P.toPairingGroupFamily d (P.G₀.encode d v₀) valW,
                ⟨⟨word, valW.coin, valW.exponent⟩ :: tabW, aborted, samples.drop (count + 1)⟩) := by
          dsimp only [blsBankWordStep]
          rw [hflW]
          simp only [Option.map_none, Option.getD_none, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, Bool.not_true, Bool.false_and, Bool.or_false, blsBankReplyWord, hdrop]
          rfl
        have hcoron :
            coronSampleWord P.toPairingGroupFamily d (P.G₀.encode d v₀) valW =
              P.G₀.encode d (P.toPairingGroupFamily.coronSampleElem d v₀ valT) := by
          unfold coronSampleWord PairingGroupFamily.coronSampleElem
          have hc : valW.coin = valT.1 := congrArg Prod.fst hval
          have hre : (valW.exponent : ZMod (P.G₀.order d)) = valT.2 := congrArg Prod.snd hval
          simp only [hc]
          cases valT.1
          · simp only [Bool.false_eq_true, ↓reduceIte, P.G₀.smul_encode, hre]
          · simp only [↓reduceIte, P.G₀.smul_encode, P.G₀.add_encode, hre]
        have htab' :
            ((⟨word, valW.coin, valW.exponent⟩ :: tabW).map
              fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
              ((word, (valT, count)) :: tabT).map fun e => (e.1, e.2.1) := by
          simp only [List.map_cons, htab, hval]
        have hvalT_def :
            (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD count
              (false, 0) = valT := rfl
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_map, wordQuery, StateT.run_bind, StateT.run_map]
        dsimp only [caller, digestEnc, samplesT, blsBankWordHandler, StateT.run, Functor.map,
          Id.run]
        rw [hstepW, hcoron]
        dsimp only [PairingGroupFamily.blsBankedReductionStep]
        rw [hfl, hid, hid, hvalT_def]
        exact ih (P.G₀.encode d (P.toPairingGroupFamily.coronSampleElem d v₀ valT))
          (⟨word, valW.coin, valW.exponent⟩ :: tabW) ((word, (valT, count)) :: tabT) aborted
          (count + 1) htab'

private theorem blsWordBankFinish_eq
    (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    (u₀ : P.G₀.Carrier d) (u₁ : P.G₁.Carrier d) (v₀ : P.G₀.Carrier d)
    (forgerCoins : List Bool) (n : ℕ)
    (samples : List BLSBankSample)
    (msig : List Bool × List Bool) (stW : BLSBankState)
    (stT : List (List Bool × ((Bool × ZMod (P.G₀.order d)) × ℕ)) × Bool × ℕ)
    (hab : stW.aborted = stT.2.1)
    (hrem : stW.remaining = samples.drop stT.2.2)
    (htab : stW.table.map (fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
      stT.1.map (fun e => (e.1, e.2.1))) :
    let caller : BLSBankCaller P.toPairingGroupFamily :=
      ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
    let samplesT : List (Bool × ZMod (P.G₀.order d)) :=
      samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))
    (P.decode₀ d (blsBankWordFinish P caller msig stW)).getD 0 =
      P.toPairingGroupFamily.blsBankedReductionFinish d u₀ samplesT
        (msig.1, (P.decode₀ d msig.2).getD 0) stT := by
  rcases stT with ⟨tabT, abortedT, countT⟩
  dsimp only at hab hrem htab
  dsimp only [blsBankWordFinish, PairingGroupFamily.blsBankedReductionFinish]
  rw [hab]
  cases habor : abortedT
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hlook :
        ((blsBankLookupEntry stW.table msig.1).map
          fun e => (e.coin, (e.exponent : ZMod (P.G₀.order d)))) =
          (tabT.lookup msig.1).map Prod.fst :=
      blsBankLookupEntry_map_eq (P.G₀.order d) msig.1 stW.table tabT htab
    have hget :
        (fun s : BLSBankSample => (s.coin, (s.exponent : ZMod (P.G₀.order d))))
          (stW.remaining.headD ⟨false, 0⟩) =
        (samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD countT
          (false, 0) := by
      rw [hrem, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop,
        List.getElem?_map]
      cases samples[countT]? <;> simp
    cases hfl : tabT.lookup msig.1 with
    | some entry =>
      rcases entry with ⟨sampleT, idxT⟩
      rw [hfl, Option.map_some] at hlook
      cases hfW : blsBankLookupEntry stW.table msig.1 with
      | none => simp [hfW] at hlook
      | some eW =>
        simp only [hfW, Option.map_some, Option.some.injEq] at hlook
        have hc : eW.coin = sampleT.1 := congrArg Prod.fst hlook
        have hre : (eW.exponent : ZMod (P.G₀.order d)) = sampleT.2 := congrArg Prod.snd hlook
        simp only [Option.map_some, Option.getD_some]
        by_cases hcoin : sampleT.1 = true
        · have hcW : eW.coin = true := hc.trans hcoin
          simp only [hcW, hcoin, ↓reduceIte]
          have hsigW :
              (if P.isElem₀ (d, msig.2) then msig.2 else P.G₀.encode d 0) =
                P.G₀.encode d ((P.decode₀ d msig.2).getD (0 : P.G₀.Carrier d)) :=
            (P.toDecodableG₀.encode_decode_getD d msig.2 (0 : P.G₀.Carrier d)).symm
          rw [hsigW, P.G₀.smul_encode, ZMod.natCast_sub_mod_eq_neg, hre, neg_smul,
            P.G₀.add_encode, ← sub_eq_add_neg, P.decode₀_encode]
          rfl
        · have hcf : sampleT.1 = false := Bool.eq_false_iff.mpr hcoin
          have hcW : eW.coin = false := hc.trans hcf
          simp only [hcW, hcf, Bool.false_eq_true, ↓reduceIte, P.decode₀_encode, Option.getD_some]
    | none =>
      rw [hfl, Option.map_none] at hlook
      cases hfW : blsBankLookupEntry stW.table msig.1 with
      | some _ => simp [hfW] at hlook
      | none =>
        have hc : (stW.remaining.headD ⟨false, 0⟩).coin =
            ((samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD countT
              (false, 0)).1 :=
          congrArg Prod.fst hget
        have hre : ((stW.remaining.headD ⟨false, 0⟩).exponent : ZMod (P.G₀.order d)) =
            ((samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD countT
              (false, 0)).2 :=
          congrArg Prod.snd hget
        simp only [Option.map_none, Option.getD_none]
        by_cases hcoin : ((samples.map fun s =>
            (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD countT (false, 0)).1 = true
        · have hcW : (stW.remaining.headD ⟨false, 0⟩).coin = true := hc.trans hcoin
          simp only [hcW, hcoin, ↓reduceIte]
          have hsigW :
              (if P.isElem₀ (d, msig.2) then msig.2 else P.G₀.encode d 0) =
                P.G₀.encode d ((P.decode₀ d msig.2).getD (0 : P.G₀.Carrier d)) :=
            (P.toDecodableG₀.encode_decode_getD d msig.2 (0 : P.G₀.Carrier d)).symm
          rw [hsigW, P.G₀.smul_encode, ZMod.natCast_sub_mod_eq_neg, hre, neg_smul,
            P.G₀.add_encode, ← sub_eq_add_neg, P.decode₀_encode]
          rfl
        · have hcf : ((samples.map fun s =>
              (s.coin, (s.exponent : ZMod (P.G₀.order d)))).getD countT (false, 0)).1 = false :=
            Bool.eq_false_iff.mpr hcoin
          have hcW : (stW.remaining.headD ⟨false, 0⟩).coin = false := hc.trans hcf
          simp only [hcW, hcf, Bool.false_eq_true, ↓reduceIte, P.decode₀_encode, Option.getD_some]
  · simp only [↓reduceIte, P.decode₀_encode, Option.getD_some]

private theorem runWith_pure_interpret_rawWordSpec {Store α : Type}
    (handler : (q : Bool × List Bool) → StateT Store Id (RawWordSpec q))
    (prog : OracleComp RawWordSpec α) (st : Store) :
    ProbOracleComp.runWith (fun req st => PMF.pure (handler req st))
        (OracleComp.interpret (fun req => ProbOracleComp.query req) prog) st =
      PMF.pure ((OracleComp.interpret handler prog).run st) := by
  induction prog using OracleComp.induction generalizing st with
  | pure a =>
    simp only [OracleComp.interpret_pure, ProbOracleComp.runWith_pure]
    rfl
  | query_bind q cont ih =>
    change ProbOracleComp.runWith (fun req st => PMF.pure (handler req st))
        (OracleComp.interpret (fun req => ProbOracleComp.query req)
          (OracleComp.query (spec := RawWordSpec) q >>= cont)) st =
      PMF.pure ((OracleComp.interpret handler
        (OracleComp.query (spec := RawWordSpec) q >>= cont)).run st)
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_query, PMF.pure_bind, StateT.run_bind]
    exact ih _ _

private theorem coCdhExperiment_blsBanked_det
    (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Bool)
    (c e keyC keyD n : ℕ)
    (α β : ZMod (P.G₀.order d)) (s : List Bool)
    (cs : Fin (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1) → Bool)
    (rhosN : Fin (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1) → ℕ) :
    let K := savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1
    let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
    let A := blsDecodedForger P d (savedCoinForger machine digestEnc c e keyC keyD n)
    let samplesW := List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)
    let samplesT := List.ofFn fun i : Fin K => (cs i, (rhosN i : ZMod (P.G₀.order d)))
    let caller : BLSBankCaller P.toPairingGroupFamily :=
      ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
        P.G₀.encode d (β • P.G₀.generator d), s, samplesW⟩
    let prog :=
      savedWordReplay machine (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
        c e keyC keyD (n, P.G₁.encode d (α • P.G₁.generator d), s)
    let wRun := (OracleComp.interpret (blsBankWordHandler P.toPairingGroupFamily caller)
      prog).run ⟨[], false, samplesW⟩
    let tRun := (OracleComp.interpret
      (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
        (β • P.G₀.generator d) samplesT)
      (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)
    (P.decode₀ d (blsBankWordFinish P caller wRun.1 wRun.2)).getD 0 =
      P.toPairingGroupFamily.blsBankedReductionFinish d (α • P.G₀.generator d) samplesT
        tRun.1 tRun.2 := by
  dsimp only
  let K := savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1
  let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
  let A := blsDecodedForger P d (savedCoinForger machine digestEnc c e keyC keyD n)
  let samplesW := List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)
  let samplesT := List.ofFn fun i : Fin K => (cs i, (rhosN i : ZMod (P.G₀.order d)))
  have hsamplesT :
      samplesW.map (fun s : BLSBankSample => (s.coin, (s.exponent : ZMod (P.G₀.order d)))) =
        samplesT := by
    simp only [samplesW, samplesT, List.map_ofFn, Function.comp_def]
  let prog :=
    savedWordReplay machine (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
      c e keyC keyD (n, P.G₁.encode d (α • P.G₁.generator d), s)
  have hA_forge :
      A.forge (α • P.G₁.generator d) s =
        Prod.map id (fun sigWord => (P.decode₀ d sigWord).getD 0) <$>
          OracleComp.interpret
            (OracleComp.sumHandler
              (fun msg => P.G₀.encode d <$>
                OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                  (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
              (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                  (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
            (OracleComp.interpret
              (fun request : Bool × List Bool => wordQuery digestEnc request.1 request.2)
              prog) := by
    change
      Prod.map id (fun sigWord => (P.decode₀ d sigWord).getD 0) <$>
        OracleComp.interpret
          (OracleComp.sumHandler
            (fun msg => P.G₀.encode d <$>
              OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
            (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
          (savedWordReplay machine (wordQuery digestEnc) c e keyC keyD
            (n, P.G₁.encode d (α • P.G₁.generator d), s)) = _
    rw [savedWordReplay_eq_interpret]
  have hstep := P.blsWordBankStep_eq_blsBankedReductionStep d (α • P.G₀.generator d)
    (α • P.G₁.generator d) (β • P.G₀.generator d) s n samplesW prog [] [] false 0 rfl
  dsimp only at hstep
  simp only [List.drop_zero] at hstep
  obtain ⟨h1, h2, h3, h4⟩ := hstep
  have ht1 :
      (OracleComp.interpret
        (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
          (β • P.G₀.generator d) samplesT)
        (A.forge (α • P.G₁.generator d) s)).run ([], false, 0) =
        (Prod.map id (fun sigWord => (P.decode₀ d sigWord).getD 0)
          ((OracleComp.interpret
            (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
              (β • P.G₀.generator d) samplesT)
            (OracleComp.interpret
              (OracleComp.sumHandler
                (fun msg => P.G₀.encode d <$>
                  OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                    (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
                (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                    (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
              (OracleComp.interpret
                (fun request : Bool × List Bool => wordQuery digestEnc request.1 request.2)
                prog))).run ([], false, 0)).1,
          ((OracleComp.interpret
            (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
              (β • P.G₀.generator d) samplesT)
            (OracleComp.interpret
              (OracleComp.sumHandler
                (fun msg => P.G₀.encode d <$>
                  OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                    (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inl msg))
                (fun q => OracleComp.query (spec := ForgerSpec (List Bool) (List Bool)
                    (P.G₀.Carrier d) (P.G₀.Carrier d)) (Sum.inr q)))
              (OracleComp.interpret
                (fun request : Bool × List Bool => wordQuery digestEnc request.1 request.2)
                prog))).run ([], false, 0)).2) := by
    rw [hA_forge, OracleComp.interpret_map, StateT.run_map]
    rfl
  rw [ht1]
  have hfin := P.blsWordBankFinish_eq d (α • P.G₀.generator d) (α • P.G₁.generator d)
    (β • P.G₀.generator d) s n samplesW
    ((OracleComp.interpret
      (blsBankWordHandler P.toPairingGroupFamily
        ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
          P.G₀.encode d (β • P.G₀.generator d), s, samplesW⟩) prog).run
      ⟨[], false, samplesW⟩).1
    ((OracleComp.interpret
      (blsBankWordHandler P.toPairingGroupFamily
        ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
          P.G₀.encode d (β • P.G₀.generator d), s, samplesW⟩) prog).run
      ⟨[], false, samplesW⟩).2
    _ (hsamplesT ▸ h2) (h3) (hsamplesT ▸ h4)
  rw [hsamplesT] at hfin
  dsimp only [K, prog, digestEnc, samplesW, samplesT] at h1 hsamplesT hfin ⊢
  simpa only [h1, hsamplesT, Prod.map, id_eq] using hfin

private noncomputable def blsBankedOutcome (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Bool)
    (c e keyC keyD n : ℕ) (α β : ZMod (P.G₀.order d)) (s : List Bool)
    (cs : Fin (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1) → Bool)
    (rhos : Fin (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1) →
      ZMod (P.G₀.order d)) : Bool :=
  let K := savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1
  let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
  let A := blsDecodedForger P d (savedCoinForger machine digestEnc c e keyC keyD n)
  let samples := List.ofFn fun i : Fin K => (cs i, rhos i)
  let res := (OracleComp.interpret
    (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
      (β • P.G₀.generator d) samples)
    (A.forge (α • P.G₁.generator d) s)).run ([], false, 0)
  decide (P.toPairingGroupFamily.blsBankedReductionFinish d (α • P.G₀.generator d)
    samples res.1 res.2 = (α * β) • P.G₀.generator d)

private theorem coCdhExperiment_blsBankedCoCDHAdversary_le
    (P : DecodablePairingGroupFamily) (d : P.G₀.Desc)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Bool)
    (c e keyC keyD n : ℕ) :
    Game.advantage
      (ProbComp.eval (coCdhExperiment (P.G₀.order d) (P.G₀.generator d) (P.G₁.generator d)
        (blsBankedCoCDHAdversary P machine c e keyC keyD n d)))
      (do
        let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let z ← P.toPairingGroupFamily.blsBankedReduction d
          (blsDecodedForger P d (savedCoinForger machine
            ⟨P.G₀.encode d, P.G₀.encode_injective d⟩ c e keyC keyD n))
          (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1)
          (ProbComp.eval (ProbComp.sampleDyadicCoin (savedCoinBudget c e keyC keyD n) 1))
          (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
        return decide (z = (α * β) • P.G₀.generator d)) ≤
      ((savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1 : ℕ) : ℝ≥0) /
        2 ^ n := by
  let budget := savedCoinBudget c e keyC keyD n
  let K := budget + budget + 1
  let coin := ProbComp.eval (ProbComp.sampleDyadicCoin budget 1)
  have hEqGame :
      ProbComp.eval (coCdhExperiment (P.G₀.order d) (P.G₀.generator d) (P.G₁.generator d)
        (blsBankedCoCDHAdversary P machine c e keyC keyD n d)) =
      (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun β =>
          (BitString.uniformList budget).bind fun s =>
            (PMF.iid coin K).bind fun cs =>
              (PMF.iid (ProbComp.eval (P.G₀.sampleExp n d)) K).bind fun rhosN =>
                PMF.pure (P.blsBankedOutcome d machine c e keyC keyD n α β s cs
                  fun i => (rhosN i : ZMod (P.G₀.order d))) := by
    dsimp only [coCdhExperiment, blsBankedCoCDHAdversary, blsBankReplay]
    simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.pure_bind,
      PMF.bind_bind, BitString.eval_sampleList, ProbComp.eval_replicate_iid, PMF.bind_map,
      Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun α _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun β _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun cs _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun rhosN _ => ?_
    have hzip :
        ((List.ofFn cs).zip (List.ofFn rhosN)).map (fun p => (⟨p.1, p.2⟩ : BLSBankSample)) =
          List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample) := by
      apply List.ext_getElem
      · simp only [List.length_map, List.length_zip, List.length_ofFn, min_self, budget, K]
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rw [hzip]
    rw [ProbOracleComp.eval_runState, savedWordReplay_eq_interpret]
    simp only [ProbComp.eval_pure, Prod.mk.eta]
    rw [show (fun q st => PMF.pure (blsBankWordStep P.toPairingGroupFamily
        ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
          P.G₀.encode d (β • P.G₀.generator d), s,
          List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)⟩ q st)) =
        (fun req st => PMF.pure (blsBankWordHandler P.toPairingGroupFamily
          ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
            P.G₀.encode d (β • P.G₀.generator d), s,
            List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)⟩ req st)) from rfl]
    rw [runWith_pure_interpret_rawWordSpec (blsBankWordHandler P.toPairingGroupFamily _),
      PMF.pure_bind]
    dsimp only [blsBankedOutcome]
    congr 1
    exact congrArg (fun z => decide (z = (α * β) • P.G₀.generator d))
      (P.coCdhExperiment_blsBanked_det d machine c e keyC keyD n α β s cs rhosN)
  have hRHS_eq :
      (do
        let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let z ← P.toPairingGroupFamily.blsBankedReduction d
          (blsDecodedForger P d (savedCoinForger machine
            ⟨P.G₀.encode d, P.G₀.encode_injective d⟩ c e keyC keyD n))
          K coin
          (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
        return decide (z = (α * β) • P.G₀.generator d)) =
      (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun β =>
          (BitString.uniformList budget).bind fun s =>
            (PMF.iid coin K).bind fun cs =>
              (PMF.iid (PMF.uniformOfFintype (ZMod (P.G₀.order d))) K).bind fun rhos =>
                PMF.pure (P.blsBankedOutcome d machine c e keyC keyD n α β s cs rhos) := by
    dsimp only [PairingGroupFamily.blsBankedReduction, blsDecodedForger, savedCoinForger]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun α _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun β _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun s _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun cs _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun rhos _ => ?_
    dsimp only [blsBankedOutcome, blsDecodedForger, savedCoinForger]
    rfl
  rw [hEqGame, hRHS_eq]
  refine Game.advantage_bind_le_nnreal _ _ _ fun α => Game.advantage_bind_le_nnreal _ _ _ fun β =>
    Game.advantage_bind_le_nnreal _ _ _ fun s => Game.advantage_bind_le_nnreal _ _ _ fun cs => ?_
  exact P.G₀.advantage_bind_iid_sampleExp_le n d K
    (fun rhos => PMF.pure (P.blsBankedOutcome d machine c e keyC keyD n α β s cs rhos))

private theorem coCdhGame_blsBankedCoCDHAdversary_le
    (P : DecodablePairingGroupFamily) (description : ℕ → P.G₀.Desc)
    {k : ℕ} {Control : Type} (machine : MultiTapePTM k Bool Control Bool)
    (c e keyC keyD n : ℕ) :
    Game.advantage
      (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m))
        (blsBankedCoCDHAdversary P machine c e keyC keyD) n)
      (do
        let d := description n
        let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
        let z ← P.toPairingGroupFamily.blsBankedReduction d
          (blsDecodedForger P d (savedCoinForger machine
            ⟨P.G₀.encode d, P.G₀.encode_injective d⟩ c e keyC keyD n))
          (savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1)
          (ProbComp.eval (ProbComp.sampleDyadicCoin (savedCoinBudget c e keyC keyD n) 1))
          (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
        return decide (z = (α * β) • P.G₀.generator d)) ≤
      ((savedCoinBudget c e keyC keyD n + savedCoinBudget c e keyC keyD n + 1 : ℕ) : ℝ≥0) /
        2 ^ n := by
  dsimp only [PrimeOrderGroupFamily.coCdhGame, Game.withSetup]
  rw [PMF.pure_bind]
  exact P.coCdhExperiment_blsBankedCoCDHAdversary_le (description n) machine c e keyC keyD n

end DecodablePairingGroupFamily

namespace PrimeOrderGroupFamily

open DecodablePairingGroupFamily

/-- **Asymptotic EUF-CMA security of native BLS signatures from co-CDH** (`[BonehShoup2023]`,
Section 15.5.1, Theorem 15.1, pp. 627–629): if `P.G₀.CoCDH P.G₁ (fun n => PMF.pure (description n))`
holds for a sequence of group descriptions with polynomially bounded encoding lengths, then
`P.blsNativeROMScheme n (description n)` (with `schnorrSigKeyGen` / `sampleExp` key generation and
deterministic per-parameter group descriptions `description n`; randomized group-generation setups
are not covered) is existentially unforgeable under chosen message attack (`ROMSignature.EUFCMA`)
against every uniform oracle-PPT word forger in the random-oracle model. -/
theorem CoCDH.eufCma_blsNativeROMScheme (P : DecodablePairingGroupFamily)
    {description : ℕ → P.G₀.Desc}
    [∀ n, Fintype (P.G₀.Carrier (description n))]
    (hCoCDH : P.G₀.CoCDH P.G₁ fun n => PMF.pure (description n))
    (hdescription : PolynomiallyBounded fun n => (P.G₀.encDesc (description n)).length) :
    ROMSignature.EUFCMA
      (fun n => ⟨P.G₀.encode (description n), P.G₀.encode_injective _⟩)
      (fun n => P.blsNativeROMScheme n (description n)) := by
  refine ROMSignature.EUFCMA.of_negligible fun program hprogram => ?_
  obtain ⟨c₁, k₁, hlen₁⟩ := P.G₁.toFamily.exists_length_encode_le
  obtain ⟨c₂, k₂, hlen₂⟩ := polynomiallyBounded_iff_le.mp hdescription
  have hpolyKey : PolynomiallyBounded fun n => c₁ * (c₂ * (n + 1) ^ k₂ + 1) ^ k₁ := by fun_prop
  obtain ⟨keyC, keyD, hkeyBound⟩ := polynomiallyBounded_iff_le.mp hpolyKey
  have hgen :
      ∀ n keys,
        keys ∈ (ProbComp.eval (P.G₁.toFamily.schnorrSigKeyGen n (description n))).support →
          keys.1.length ≤ keyC * (n + 1) ^ keyD := by
    intro n keys hkeys
    rw [PrimeOrderGroupFamily.eval_schnorrSigKeyGen, PMF.mem_support_map_iff] at hkeys
    dsimp only [PrimeOrderGroupFamily.Companion.toFamily] at hkeys
    obtain ⟨α, _, rfl⟩ := hkeys
    have h1 := hlen₁ (description n) (α • P.G₁.generator (description n))
    have h2 : (P.G₁.toFamily.encDesc (description n)).length ≤ c₂ * (n + 1) ^ k₂ := hlen₂ n
    exact h1.trans ((Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.succ_le_succ h2) k₁)).trans
      (hkeyBound n))
  obtain ⟨k, Control, hfinite, machine, c, e, -, hgame⟩ :=
    exists_eufCmaGame_savedCoinForger
      (gen := fun n => P.G₁.toFamily.schnorrSigKeyGen n (description n))
      hgen hprogram
  let adv := P.blsBankedCoCDHAdversary machine c e keyC keyD
  have hbreak : Negligible fun n =>
      Game.succProbability (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) :=
    hCoCDH adv (P.isPPT_blsBankedCoCDHAdversary machine c e keyC keyD)
  let budget := savedCoinBudget c e keyC keyD
  let K (n : ℕ) := budget n + budget n + 1
  have hbudget : PolynomiallyBounded budget := polynomiallyBounded_savedCoinBudget c e keyC keyD
  have hK : PolynomiallyBounded K := by
    dsimp only [K]
    fun_prop
  have hBoundReal :
      ∀ n,
        (Game.succProbability
          (wordEufCmaGame ⟨P.G₀.encode (description n), P.G₀.encode_injective _⟩
            (P.blsNativeROMScheme n (description n)) (program n)) : ℝ) ≤
          (3 * (2 * (budget n + 1 : ℕ) : ℕ) : ℕ) *
            ((Game.succProbability
              (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
              (K n : ℝ) / 2 ^ n) +
            (1 : ℝ) / 2 ^ n := by
    intro n
    let d := description n
    let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
    let Aword := savedCoinForger machine digestEnc c e keyC keyD n
    obtain ⟨hcb, heqGame⟩ := hgame n (P.G₀.Carrier d) digestEnc (P.blsNativeROMScheme n d) rfl
    rw [heqGame]
    have hnat := P.succProbability_eufCmaGame_blsNativeROMScheme_le n d Aword
    let A := blsDecodedForger P d Aword
    have hcbA := P.callBounded_blsDecodedForger d hcb
    let coin := ProbComp.eval (ProbComp.sampleDyadicCoin (budget n) 1)
    have hcoin : (coin true).toReal = (dyadicSize (budget n) : ℝ)⁻¹ := by
      dsimp only [coin]
      rw [ProbComp.eval_sampleDyadicCoin_true_toReal]
      have hpos : 1 ≤ dyadicSize (budget n) := dyadicSize_pos (budget n)
      simp [Nat.min_eq_right hpos, one_div]
    have ha : (budget n + 1 : ℝ) ≤ dyadicSize (budget n) := by
      exact_mod_cast lt_dyadicSize (budget n)
    have hcoron := P.toPairingGroupFamily.succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked
      d A hcbA coin hcoin ha
    have hadv := Game.coe_succProbability_le_add_of_advantage_le
      (NNReal.coe_le_coe.mpr ((Game.advantage_comm _ _).trans_le
        (P.coCdhGame_blsBankedCoCDHAdversary_le description machine c e keyC keyD n)))
    have hdy : (dyadicSize (budget n) : ℝ) ≤ (2 * (budget n + 1) : ℕ) := by
      exact_mod_cast dyadicSize_le (budget n)
    have hK_eq : budget n + budget n + 1 = K n := rfl
    rw [hK_eq] at hadv
    have hprob0 :
        0 ≤ (Game.succProbability
          (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
          (K n : ℝ) / 2 ^ n := by positivity
    calc
      (Game.succProbability (eufCmaGame (P.blsNativeROMScheme n d) Aword) : ℝ)
          ≤ (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d) A) :
              ℝ) + 1 / 2 ^ n := hnat
      _ ≤ 2.72 * (dyadicSize (budget n) : ℝ) *
            (Game.succProbability (do
              let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
              let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
              let z ← P.toPairingGroupFamily.blsBankedReduction d A (K n) coin
                (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
              return decide (z = (α * β) • P.G₀.generator d)) : ℝ) + 1 / 2 ^ n := by
          gcongr
      _ ≤ 2.72 * (dyadicSize (budget n) : ℝ) *
            ((Game.succProbability
              (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
              (K n : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
          push_cast at hadv
          exact add_le_add (mul_le_mul_of_nonneg_left hadv
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2.72) (Nat.cast_nonneg _))) le_rfl
      _ ≤ 3 * (2 * (budget n + 1 : ℕ) : ℕ) *
            ((Game.succProbability
              (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
              (K n : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
          exact add_le_add (mul_le_mul_of_nonneg_right
            (mul_le_mul (by norm_num : (2.72 : ℝ) ≤ 3) hdy (Nat.cast_nonneg _)
              (by norm_num : (0 : ℝ) ≤ 3)) hprob0) le_rfl
      _ = (3 * (2 * (budget n + 1 : ℕ) : ℕ) : ℕ) *
            ((Game.succProbability
              (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
              (K n : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
          push_cast; ring
  have hpolyMul : PolynomiallyBounded (fun n => 3 * (2 * (budget n + 1))) := by fun_prop
  have hKdiv : Negligible (fun n => (K n : ℝ≥0) / 2 ^ n) :=
    Negligible.polynomiallyBounded_div hK negligible_inv_two_pow
  have hsum : Negligible (fun n =>
      ((3 * (2 * (budget n + 1)) : ℕ) : ℝ≥0) *
        (Game.succProbability
          (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) +
          (K n : ℝ≥0) / 2 ^ n) + (1 : ℝ≥0) / 2 ^ n) :=
    ((hbreak.add hKdiv).polynomiallyBounded_mul hpolyMul).add negligible_one_div_two_pow
  refine negligible_of_le hsum fun n => ?_
  have h := hBoundReal n
  rw [← NNReal.coe_le_coe]
  push_cast at h ⊢
  exact h

/-- **Asymptotic SUF-CMA security of native BLS signatures from co-CDH** (`[BonehShoup2023]`,
Section 15.5.1, Theorem 15.1, pp. 627–629): strong existential unforgeability follows directly from
`CoCDH.eufCma_blsNativeROMScheme` and canonical signature uniqueness
(`DecodablePairingGroupFamily.sufCma_iff_eufCma_blsNativeROMScheme`). -/
theorem CoCDH.sufCma_blsNativeROMScheme (P : DecodablePairingGroupFamily)
    {description : ℕ → P.G₀.Desc}
    [∀ n, Fintype (P.G₀.Carrier (description n))]
    (hCoCDH : P.G₀.CoCDH P.G₁ fun n => PMF.pure (description n))
    (hdescription : PolynomiallyBounded fun n => (P.G₀.encDesc (description n)).length) :
    ROMSignature.SUFCMA
      (fun n => ⟨P.G₀.encode (description n), P.G₀.encode_injective _⟩)
      (fun n => P.blsNativeROMScheme n (description n)) :=
  (P.sufCma_iff_eufCma_blsNativeROMScheme description).mpr
    (CoCDH.eufCma_blsNativeROMScheme P hCoCDH hdescription)

end PrimeOrderGroupFamily

end Cslib.Crypto
