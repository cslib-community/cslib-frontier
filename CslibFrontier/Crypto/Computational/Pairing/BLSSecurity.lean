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
  have hd : ComputableInPolyTime (fun p : _ => p.1) E P.G₀.encDesc := by fun_prop
  have hc : ComputableInPolyTime (fun p : _ => p.2.2.coin) E encBool := by fun_prop
  have hmask := P.G₀.computableInPolyTime_smul.comp
    (hd.prod (ComputableInPolyTime.prod (f := fun p => p.2.2.exponent) (by fun_prop)
      (PrimeOrderGroupFamily.computableInPolyTime_encode_generator hd)))
  exact (hc.ite (P.G₀.computableInPolyTime_add.comp
    (hd.prod (ComputableInPolyTime.prod (f := fun p => p.2.1) (by fun_prop) hmask)))
      hmask).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_blsBankReplyWord (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun p : P.G₀.Desc × List Bool × List Bool × Bool × BLSBankSample =>
        blsBankReplyWord P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair P.G₀.encDesc (encPair encBits (encPair encBits (encPair encBool encBLSBankSample))))
      encBits := by
  let E := encPair P.G₀.encDesc
    (encPair encBits (encPair encBits (encPair encBool encBLSBankSample)))
  have hd : ComputableInPolyTime (fun p : _ => p.1) E P.G₀.encDesc := by fun_prop
  have hhash : ComputableInPolyTime (fun p : _ => p.2.2.2.1) E encBool := by fun_prop
  have hcoin : ComputableInPolyTime (fun p : _ => p.2.2.2.2.coin) E encBool := by fun_prop
  exact (hhash.ite ((computableInPolyTime_coronSampleWord P).comp
      (hd.prod (ComputableInPolyTime.prod (by fun_prop) (by fun_prop))))
    (hcoin.ite (PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd)
      (P.G₀.computableInPolyTime_smul.comp
        (hd.prod (ComputableInPolyTime.prod (by fun_prop) (by fun_prop)))))).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_blsBankLookupEntry {α : Type} {encIn : α ↪ List Bool}
    {tab : α → List BLSBankEntry} {q : α → List Bool}
    (htab : ComputableInPolyTime tab encIn (encList encBLSBankEntry))
    (hq : ComputableInPolyTime q encIn encBits) :
    ComputableInPolyTime (fun a => blsBankLookupEntry (tab a) (q a))
      encIn (encOption encBLSBankEntry) :=
  ComputableInPolyTime.findWith (test := fun x : List Bool × BLSBankEntry => x.1 == x.2.query)
    ((by fun_prop : ComputableInPolyTime (fun x : List Bool × BLSBankEntry => x.1)
      (encPair encBits encBLSBankEntry) encBits).beq (by fun_prop)) hq htab

private theorem computableInPolyTime_blsBankSelectSample {α : Type} {encIn : α ↪ List Bool}
    {st : α → BLSBankState} {q : α → List Bool}
    (hst : ComputableInPolyTime st encIn encBLSBankState)
    (hq : ComputableInPolyTime q encIn encBits) :
    ComputableInPolyTime
      (fun a => ((blsBankLookupEntry (st a).table (q a)).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)).getD ((st a).remaining.headD ⟨false, 0⟩))
      encIn encBLSBankSample := by
  have hfound := computableInPolyTime_blsBankLookupEntry
    ((by fun_prop : ComputableInPolyTime BLSBankState.table encBLSBankState _).comp hst) hq
  have hopt : ComputableInPolyTime
      (fun a => (blsBankLookupEntry (st a).table (q a)).map
        fun e => (⟨e.coin, e.exponent⟩ : BLSBankSample)) encIn (encOption encBLSBankSample) :=
    ComputableInPolyTime.optionMapWithInput hfound
      ((encBLSBankSample_mk_polyTime
        (by fun_prop : ComputableInPolyTime (fun x : α × BLSBankEntry => x.2.coin)
          (encPair encIn encBLSBankEntry) encBool)
        (by fun_prop : ComputableInPolyTime (fun x : α × BLSBankEntry => x.2.exponent)
          (encPair encIn encBLSBankEntry) encNat)).of_enc_eq fun _ => rfl)
  have hdef := (ComputableInPolyTime.headD (encA := encBLSBankSample) ⟨false, 0⟩).comp
    ((by fun_prop : ComputableInPolyTime BLSBankState.remaining encBLSBankState _).comp hst)
  exact ComputableInPolyTime.optionGetDWithInput hopt hdef

private theorem computableInPolyTime_blsBankWordStep (P : PairingGroupFamily) :
    ComputableInPolyTime
      (fun p : BLSBankCaller P × (Bool × List Bool) × BLSBankState =>
        blsBankWordStep P p.1 p.2.1 p.2.2)
      (encHandlerCall (encBLSBankCaller P) (encFinEnum Bool) encBLSBankState)
      (encPair encBits encBLSBankState) := by
  let E := encHandlerCall (encBLSBankCaller P) (encFinEnum Bool) encBLSBankState
  have hr : ComputableInPolyTime (fun p : _ => p.2.1) E (encPair (encFinEnum Bool) encBits) := by
    fun_prop
  have hop : ComputableInPolyTime (fun p : _ => p.2.1.1) E encBool :=
    (ComputableInPolyTime.of_finite (id : Bool → Bool) (encIn := encFinEnum Bool)
      (encOut := encBool)).comp ((ComputableInPolyTime.fst (encFinEnum Bool) encBits).comp hr)
  have hword : ComputableInPolyTime (fun p : _ => p.2.1.2) E encBits :=
    (ComputableInPolyTime.snd (encFinEnum Bool) encBits).comp hr
  have hst : ComputableInPolyTime (fun p : _ => p.2.2) E encBLSBankState := by fun_prop
  have htab : ComputableInPolyTime (fun p : _ => p.2.2.table) E (encList encBLSBankEntry) := by
    fun_prop
  have hfound := computableInPolyTime_blsBankLookupEntry htab hword
  have hsample := computableInPolyTime_blsBankSelectSample hst hword
  have hsc := (by fun_prop : ComputableInPolyTime BLSBankSample.coin encBLSBankSample encBool).comp
    hsample
  have hsr := (by fun_prop : ComputableInPolyTime BLSBankSample.exponent encBLSBankSample
    encNat).comp hsample
  have hnewEntry := (encBLSBankEntry_mk_polyTime hword hsc hsr).of_enc_eq fun _ => rfl
  have htable' := ((ComputableInPolyTime.optionIsSome hfound).ite htab
    ((ComputableInPolyTime.cons encBLSBankEntry).comp (hnewEntry.prod htab))).of_enc_eq fun _ => rfl
  have haborted' := ComputableInPolyTime.bool_or'
    (by fun_prop : ComputableInPolyTime (fun p : _ => p.2.2.aborted) E encBool)
    (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_not.comp hop) hsc)
  have hrem' := (ComputableInPolyTime.listTail encBLSBankSample).comp
    (by fun_prop : ComputableInPolyTime (fun p : _ => p.2.2.remaining) E _)
  have hstate' := (encBLSBankState_mk_polyTime htable' haborted' hrem').of_enc_eq fun _ => rfl
  have hd : ComputableInPolyTime (fun p : _ => p.1.groupParameters) E P.G₀.encDesc := by fun_prop
  have hu : ComputableInPolyTime (fun p : _ => p.1.leftZeroWord) E encBits := by fun_prop
  have hv : ComputableInPolyTime (fun p : _ => p.1.rightZeroWord) E encBits := by fun_prop
  have hreply := (computableInPolyTime_blsBankReplyWord P).comp
    (hd.prod (hu.prod (hv.prod (hop.prod hsample))))
  exact (hreply.prod hstate').of_enc_eq fun _ => rfl

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
  have hsig : ComputableInPolyTime (fun p : _ => p.2.1.2) E encBits := by fun_prop
  have hsample := computableInPolyTime_blsBankSelectSample
    (by fun_prop : ComputableInPolyTime (fun p : _ => p.2.2) E encBLSBankState)
    (by fun_prop : ComputableInPolyTime (fun p : _ => p.2.1.1) E encBits)
  have hcoin := (by fun_prop : ComputableInPolyTime BLSBankSample.coin encBLSBankSample
    encBool).comp hsample
  have hexp := (by fun_prop : ComputableInPolyTime BLSBankSample.exponent encBLSBankSample
    encNat).comp hsample
  have hzero := PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd
  have hq := P.G₀.computableInPolyTime_order.comp hd
  have hsigWord := (P.computableInPolyTime_isElem₀_app hd hsig).ite hsig hzero
  have hadd := P.G₀.computableInPolyTime_add.comp
    (hd.prod (hsigWord.prod
      (P.G₀.computableInPolyTime_smul.comp
        (hd.prod ((hq.binary_sub' (hexp.binary_mod' hq)).prod hu)))))
  exact ((by fun_prop : ComputableInPolyTime (fun p : _ => p.2.2.aborted) E encBool).ite hzero
    (hcoin.ite hadd hzero)).of_enc_eq fun _ => rfl

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
      (encBLSBankCaller P) encReplayInput :=
    (ComputableInPolyTime.prod (by fun_prop)
      (ComputableInPolyTime.prod (by fun_prop) (by fun_prop))).of_enc_eq fun _ => rfl
  have hinitial : ComputableInPolyTime
      (fun caller : BLSBankCaller P => (⟨[], false, caller.bank⟩ : BLSBankState))
      (encBLSBankCaller P) encBLSBankState :=
    (encBLSBankState_mk_polyTime (ComputableInPolyTime.const [])
      (ComputableInPolyTime.const false) (by fun_prop)).of_enc_eq fun _ => rfl
  have hresources : ComputableInPolyTime
      (fun pair : BLSBankCaller P × List Bool => resources pair.1 pair.2)
      (encPair (encBLSBankCaller P) encBits) encUnary := by
    let E := encPair (encBLSBankCaller P) encBits
    have hmul (k : ℕ) {f : BLSBankCaller P × List Bool → ℕ}
        (hf : ComputableInPolyTime f E encUnary) :=
      ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const k).prod hf)
    have hadd {f g : BLSBankCaller P × List Bool → ℕ}
        (hf : ComputableInPolyTime f E encUnary) (hg : ComputableInPolyTime g E encUnary) :=
      ComputableInPolyTime.unary_add.comp (hf.prod hg)
    have hbankMax : ComputableInPolyTime (fun p : _ => bankMax p.1) E encUnary :=
      hadd ((ComputableInPolyTime.encoding_length (encList encBLSBankSample)).comp (by fun_prop))
        (.const (encBLSBankSample ⟨false, 0⟩).length)
    have hargLen : ComputableInPolyTime (fun p : _ => argLen p.1) E encUnary :=
      hadd (hadd (hadd (hadd
        (hmul 2 ((ComputableInPolyTime.encoding_length P.G₀.encDesc).comp (by fun_prop)))
        (hmul 2 (ComputableInPolyTime.length_bits.comp (by fun_prop))))
        (hmul 2 (ComputableInPolyTime.length_bits.comp (by fun_prop)))) hbankMax) (.const 64)
    have hleft := hmul cR
      ((ComputableInPolyTime.unary_pow dR).comp (hadd hargLen (.const 1)))
    have hright := hadd (hadd (hmul 8
      (ComputableInPolyTime.length_bits.comp (ComputableInPolyTime.snd _ _)))
      (hmul 4 hbankMax)) (.const 64)
    exact ComputableInPolyTime.unary_max.comp (hleft.prod hright)
  refine IsOraclePPTOn.isPPTOn_runState (isOraclePPTOn_savedWordReplay machine c e keyC keyD)
    hprepare (computableInPolyTime_blsBankWordStep P).isPPTOn hinitial invariant
    (fun caller => ⟨fun _ h => (by cases h), fun s hs =>
      (length_le_encList_of_mem encBLSBankSample hs).trans (Nat.le_add_right _ _)⟩)
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
      simpa only [sample, hf, Option.map_some, Option.getD_some] using
        hinv.1 entry (List.mem_of_find?_eq_some hf)
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
        exact hentry.elim (fun h => h ▸ hsampleLen) (hinv.1 entry)
    · cases hrem : state.remaining with
      | nil => simp [hrem] at hs
      | cons hd tl => exact hinv.2 s (hrem ▸ List.mem_cons_of_mem _ (by simpa [hrem] using hs))
  have hreplyLen :
      (blsBankReplyWord P caller.groupParameters caller.leftZeroWord caller.rightZeroWord
        request.1 sample).length ≤ resources caller request.2 := by
    refine (hlenR (caller.groupParameters, caller.leftZeroWord, caller.rightZeroWord,
      request.1, sample)).trans ((Nat.mul_le_mul_left cR (Nat.pow_le_pow_left ?_ dR)).trans
      (le_max_left _ _))
    have hbool : (encBool request.1).length = 1 := by cases request.1 <;> rfl
    dsimp only [argLen]
    enc_len
  have hstateLen :
      (encBLSBankState
        ⟨if found.isSome then state.table
          else ⟨request.2, sample.coin, sample.exponent⟩ :: state.table,
          state.aborted || (!request.1 && sample.coin), state.remaining.tail⟩).length ≤
        (encBLSBankState state).length + resources caller request.2 := by
    have htail := length_encList_tail_le encBLSBankSample state.remaining
    have habEq : (encBool (state.aborted || (!request.1 && sample.coin))).length =
        (encBool state.aborted).length := by
      cases state.aborted <;> cases request.1 <;> cases sample.coin <;> rfl
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
        have hboolS : (encBool sample.coin).length = 1 := by cases sample.coin <;> rfl
        simp only [encBLSBankSample_apply, length_encPair, hboolS] at hsampleLen
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
  have hn0 := F.encCoCDHInput_secParam_polyTime C ComputableInPolyTime.id'
  have h1 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hn0)
  have h2 := ComputableInPolyTime.unary_add.comp (h1.prod (.const 2))
  have h3 := ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const keyC).prod
    ((ComputableInPolyTime.unary_pow keyD).comp
      (ComputableInPolyTime.unary_add.comp (hn0.prod (.const 1)))))
  exact ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const c).prod
    ((ComputableInPolyTime.unary_pow e).comp (ComputableInPolyTime.unary_add.comp (h2.prod h3))))

private theorem computableInPolyTime_blsBankAdversaryCaller (P : PairingGroupFamily) :
    ComputableInPolyTime
      (blsBankAdversaryCaller P)
      (encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
        (encList encNat))
      (encBLSBankCaller P) := by
  have hp := ComputableInPolyTime.id' (encIn :=
    encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
      (encList encNat))
  have hx := hp.fst'.fst'.fst'
  have hbank :=
    (ComputableInPolyTime.map (encA := encPair encBool encNat) (encB := encBLSBankSample)
      ((encBLSBankSample_mk_polyTime (ComputableInPolyTime.fst encBool encNat)
        (ComputableInPolyTime.snd encBool encNat)).of_enc_eq fun _ => rfl)).comp
      ((ComputableInPolyTime.zip encBool encNat).comp (hp.fst'.snd'.prod hp.snd'))
  exact (encBLSBankCaller_mk_polyTime P
    (P.G₀.encCoCDHInput_secParam_polyTime P.G₁ hx)
    (P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ hx)
    (P.G₀.encCoCDHInput_leftZero_polyTime P.G₁ hx)
    (P.G₀.encCoCDHInput_leftOne_polyTime P.G₁ hx)
    (P.G₀.encCoCDHInput_rightZero_polyTime P.G₁ hx)
    hp.fst'.fst'.snd' hbank).of_enc_eq fun _ => rfl

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
  have hq := ComputableInPolyTime.id' (encIn := encPair
    (encPair (encPair (encPair (P.G₀.encCoCDHInput P.G₁) encBits) (encList encBool))
      (encList encNat))
    (encPair (encPair encBits encBits) encBLSBankState))
  have hout := (computableInPolyTime_blsBankWordFinish P).comp
    (((computableInPolyTime_blsBankAdversaryCaller P.toPairingGroupFamily).comp
      hq.fst').prod hq.snd')
  have hd4 := P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ hq.fst'.fst'.fst'.fst'
  exact ((P.computableInPolyTime_isElem₀_app hd4 hout).ite hout
    (PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd4)).of_enc_eq fun _ => rfl

/-- **The explicit banked co-CDH reduction is uniform strict PPT** (`[BonehShoup2023]`,
Theorem 15.1, pp. 628–629). -/
theorem isPPT_blsBankedCoCDHAdversary (P : DecodablePairingGroupFamily)
    {k : ℕ} {Control : Type} [Finite Control]
    (machine : MultiTapePTM k Bool Control Bool) (c e keyC keyD : ℕ) :
    (blsBankedCoCDHAdversary P machine c e keyC keyD).IsPPT := by
  dsimp only [PrimeOrderGroupFamily.CoCDHAdversary.IsPPT]
  have hn0 := P.G₀.encCoCDHInput_secParam_polyTime P.G₁ ComputableInPolyTime.id'
  have hd0 := P.G₀.encCoCDHInput_groupParameters_polyTime P.G₁ ComputableInPolyTime.id'
  have hbud0 := computableInPolyTime_savedCoinBudget P.G₀ P.G₁ c e keyC keyD
  have hbud1 := hbud0.comp (ComputableInPolyTime.fst (P.G₀.encCoCDHInput P.G₁) encBits)
  have hK1 := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_add.comp (hbud1.prod hbud1)).prod (.const 1))
  have hcs1 := (isPPTOn_sampleDyadicCoin hbud1 (ComputableInPolyTime.const 1)).replicate hK1
  have hfst2 := ComputableInPolyTime.fst (encPair (P.G₀.encCoCDHInput P.G₁) encBits)
    (encList encBool)
  have hx2 := (ComputableInPolyTime.fst (P.G₀.encCoCDHInput P.G₁) encBits).comp hfst2
  have hrhos2 := (P.G₀.isPPTOn_sampleExp (hn0.comp hx2) (hd0.comp hx2)).replicate (hK1.comp hfst2)
  have hrun := (isPPTOn_blsBankReplay P.toPairingGroupFamily machine c e keyC keyD).preprocess
    (computableInPolyTime_blsBankAdversaryCaller P.toPairingGroupFamily)
  have hcomp := hbud0.sampleList.keep_input.bind
    (hcs1.keep_input.bind (hrhos2.keep_input.bind
      (hrun.keep_input.bind (computableInPolyTime_blsBankAdversaryFinish P).isPPTOn)))
  refine hcomp.congr fun x => ?_
  dsimp only [blsBankedCoCDHAdversary, blsBankAdversaryCaller]
  simp only [ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
    PMF.bind_map, Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun s _ =>
    PMF.bind_congr_on_support _ _ _ fun cs _ =>
      PMF.bind_congr_on_support _ _ _ fun rhos _ =>
        PMF.bind_congr_on_support _ _ _ fun res _ => ?_
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
  have hcloseGame :
      CloseTo (eufCmaGame (P.blsNativeROMScheme n d) A) (eufCmaGame idealScheme A)
        ((1 : ℝ≥0) / 2 ^ n : ℝ≥0) :=
    (P.G₁.toFamily.closeTo_schnorrSigKeyGen n d).symm.bind_left _
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
    refine PMF.bind_apply_mono_on_support _ _ fun α _ =>
      PMF.bind_apply_mono_on_support _ _ fun s _ => ?_
    dsimp only
    rw [show handler idealScheme = handler (P.blsNativeROMScheme n d) from rfl,
      interpret_handler_blsNative_eq_decoded]
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
      have hσ' : P.G₀.encode d σ = forged.1.2 := hσ
      rw [← hσ', P.pairEncoded_encode, P.pairEncoded_encode,
        (P.GT.encode_injective d).eq_iff] at hpair
      have hbeq : @List.contains (List Bool) List.instBEq forged.2.2 forged.1.1 =
          @List.contains (List Bool) instBEqOfDecidableEq forged.2.2 forged.1.1 :=
        Bool.eq_iff_iff.mpr (by simp)
      have hfresh' : @List.contains (List Bool) instBEqOfDecidableEq forged.2.2 forged.1.1 =
          false := by simpa only [hbeq, Bool.not_eq_true'] using hfresh
      exact hwin2 (by
        simp only [show P.decode₀ d forged.1.2 = some σ from hdec, Option.getD_some, hpair,
          hfresh', Bool.not_false, decide_true, Bool.true_and])
    · exact zero_le
    · exact zero_le
  calc
    (Game.succProbability (eufCmaGame (P.blsNativeROMScheme n d) A) : ℝ)
        ≤ (Game.succProbability (eufCmaGame idealScheme A) : ℝ) +
            ((1 : ℝ≥0) / 2 ^ n : ℝ) := hadv
    _ ≤ (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d)
          (blsDecodedForger P d A)) : ℝ) + (1 : ℝ) / 2 ^ n := by
        push_cast
        exact add_le_add (mod_cast hideal_le) le_rfl

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
      obtain ⟨hqhd, hvalhd⟩ := Prod.mk.inj hhd
      dsimp only [blsBankLookupEntry]
      rw [List.find?_cons, List.lookup_cons_eq_ite]
      by_cases heq : key = hdW.query
      · simp [heq, hqhd, hvalhd]
      · have hne' : key ≠ hdT.1 := fun h => heq (h.trans hqhd.symm)
        simpa [blsBankLookupEntry, beq_false_of_ne heq, hne', beq_iff_eq] using ihW tlT htl

private theorem blsBankSelectSample_eq (q : ℕ) (key : List Bool)
    (samples : List BLSBankSample) (stW : BLSBankState)
    (tabT : List (List Bool × ((Bool × ZMod q) × ℕ))) (count : ℕ)
    (hrem : stW.remaining = samples.drop count)
    (htab : stW.table.map (fun e => (e.query, (e.coin, (e.exponent : ZMod q)))) =
      tabT.map (fun e => (e.1, e.2.1))) :
    let sW : BLSBankSample :=
      ((blsBankLookupEntry stW.table key).map fun e => ⟨e.coin, e.exponent⟩).getD
        (stW.remaining.headD ⟨false, 0⟩)
    (sW.coin, (sW.exponent : ZMod q)) =
      ((tabT.lookup key).map Prod.fst).getD
        ((samples.map fun s => (s.coin, (s.exponent : ZMod q))).getD count (false, 0)) := by
  have hlook := blsBankLookupEntry_map_eq q key stW.table tabT htab
  have hdef : (fun s : BLSBankSample => (s.coin, (s.exponent : ZMod q)))
      (stW.remaining.headD ⟨false, 0⟩) =
      (samples.map fun s => (s.coin, (s.exponent : ZMod q))).getD count (false, 0) := by
    rw [hrem, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop,
      List.getElem?_map]
    cases samples[count]? <;> simp
  cases hfW : blsBankLookupEntry stW.table key <;> cases hfT : tabT.lookup key <;>
    simp_all

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
    rcases q with ⟨op, word⟩
    let stW : BLSBankState := ⟨tabW, aborted, samples.drop count⟩
    have hlook := blsBankLookupEntry_map_eq (P.G₀.order d) word tabW tabT htab
    have hsel := blsBankSelectSample_eq (P.G₀.order d) word samples stW tabT count rfl htab
    have hisSome : (blsBankLookupEntry tabW word).isSome = (tabT.lookup word).isSome := by
      simpa only [Option.isSome_map] using congrArg Option.isSome hlook
    let sW : BLSBankSample :=
      ((blsBankLookupEntry stW.table word).map fun e => ⟨e.coin, e.exponent⟩).getD
        (stW.remaining.headD ⟨false, 0⟩)
    let samplesT := samples.map fun s => (s.coin, (s.exponent : ZMod (P.G₀.order d)))
    let sT := ((tabT.lookup word).map Prod.fst).getD (samplesT.getD count (false, 0))
    have hs : (sW.coin, (sW.exponent : ZMod (P.G₀.order d))) = sT := hsel
    have hc : sW.coin = sT.1 := congrArg Prod.fst hs
    have hre : (sW.exponent : ZMod (P.G₀.order d)) = sT.2 := congrArg Prod.snd hs
    have hdrop : (samples.drop count).tail = samples.drop (count + 1) := List.tail_drop ..
    have hid : ∀ {α β : Type} (x : α) (f : α → Id β), Bind.bind (m := Id) x f = f x :=
      fun _ _ => rfl
    have htab_cons :
        ((⟨word, sW.coin, sW.exponent⟩ :: tabW).map
          fun e => (e.query, (e.coin, (e.exponent : ZMod (P.G₀.order d))))) =
          ((word, (sT, count)) :: tabT).map fun e => (e.1, e.2.1) := by
      simp only [List.map_cons, htab, hs]
    have hstepW :
        blsBankWordStep P.toPairingGroupFamily
          ⟨n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀, forgerCoins, samples⟩
          (op, word) stW =
          (blsBankReplyWord P.toPairingGroupFamily d (P.G₀.encode d u₀) (P.G₀.encode d v₀) op sW,
            ⟨if (blsBankLookupEntry tabW word).isSome then tabW
              else ⟨word, sW.coin, sW.exponent⟩ :: tabW,
              aborted || (!op && sW.coin), samples.drop (count + 1)⟩) := by
      simp only [blsBankWordStep, stW, sW, hdrop]
    dsimp only
    rw [show PFunctor.FreeM.bind (OracleComp.query (spec := RawWordSpec) (op, word)) cont =
      (OracleComp.query (spec := RawWordSpec) (op, word) >>= cont) from rfl]
    cases op with
    | false =>
      have hrep : blsBankReplyWord P.toPairingGroupFamily d (P.G₀.encode d u₀) (P.G₀.encode d v₀)
          false sW = P.G₀.encode d (if sT.1 then 0 else sT.2 • u₀) := by
        dsimp only [blsBankReplyWord]
        rw [hc]
        cases sT.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, P.G₀.smul_encode, hre]
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_map,
        wordQuery, StateT.run_bind, StateT.run_map]
      dsimp only [blsBankWordHandler, StateT.run, Functor.map, Id.run,
        PairingGroupFamily.blsBankedReductionStep]
      rw [hstepW, hrep, hisSome, hid, hid]
      cases hfl : tabT.lookup word with
      | some entry =>
        rcases entry with ⟨⟨cT, ρT⟩, idxT⟩
        have hsT : sT = (cT, ρT) := by simp only [sT, hfl, Option.map_some, Option.getD_some]
        simp only [Option.isSome_some, ↓reduceIte, Bool.not_false, Bool.true_and, hc, hsT]
        cases cT <;>
          (simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_true, Bool.or_false]
           exact ih _ tabW tabT _ (count + 1) htab)
      | none =>
        have hsT : sT = samplesT.getD count (false, 0) := by
          simp only [sT, hfl, Option.map_none, Option.getD_none]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          Bool.true_and, hc, hsT]
        rw [hc, hsT] at htab_cons
        cases hc' : (samplesT.getD count (false, 0)).1 <;>
          (simp only [hc', Bool.false_eq_true, ↓reduceIte, Bool.or_true, Bool.or_false]
             at htab_cons ⊢
           exact ih _ _ _ _ (count + 1) htab_cons)
    | true =>
      have hrep : blsBankReplyWord P.toPairingGroupFamily d (P.G₀.encode d u₀) (P.G₀.encode d v₀)
          true sW = P.G₀.encode d (P.toPairingGroupFamily.coronSampleElem d v₀ sT) := by
        dsimp only [blsBankReplyWord, coronSampleWord, PairingGroupFamily.coronSampleElem]
        rw [hc]
        cases sT.1 <;>
          simp only [Bool.false_eq_true, ↓reduceIte, P.G₀.smul_encode, P.G₀.add_encode, hre]
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_map,
        wordQuery, StateT.run_bind, StateT.run_map]
      dsimp only [blsBankWordHandler, StateT.run, Functor.map, Id.run,
        PairingGroupFamily.blsBankedReductionStep]
      rw [hstepW, hrep, hisSome, hid, hid]
      cases hfl : tabT.lookup word with
      | some entry =>
        have hsT : sT = entry.1 := by simp only [sT, hfl, Option.map_some, Option.getD_some]
        simp only [Option.isSome_some, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.or_false,
          hsT]
        exact ih _ tabW tabT aborted (count + 1) htab
      | none =>
        have hsT : sT = samplesT.getD count (false, 0) := by
          simp only [sT, hfl, Option.map_none, Option.getD_none]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
          Bool.false_and, Bool.or_false, hsT]
        rw [hsT] at htab_cons
        exact ih _ _ _ aborted (count + 1) htab_cons

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
  intro caller samplesT
  rcases stT with ⟨tabT, abortedT, countT⟩
  dsimp only at hab hrem htab
  cases abortedT with
  | true =>
    dsimp only [blsBankWordFinish, PairingGroupFamily.blsBankedReductionFinish, caller]
    rw [hab]
    simp only [↓reduceIte, P.decode₀_encode, Option.getD_some]
  | false =>
    let sW : BLSBankSample :=
      ((blsBankLookupEntry stW.table msig.1).map fun e => ⟨e.coin, e.exponent⟩).getD
        (stW.remaining.headD ⟨false, 0⟩)
    let sT := ((tabT.lookup msig.1).map Prod.fst).getD (samplesT.getD countT (false, 0))
    have hfinT :
        P.toPairingGroupFamily.blsBankedReductionFinish d u₀ samplesT
          (msig.1, (P.decode₀ d msig.2).getD 0) (tabT, false, countT) =
          if sT.1 then (P.decode₀ d msig.2).getD 0 - sT.2 • u₀ else 0 := by
      unfold PairingGroupFamily.blsBankedReductionFinish
      cases hfl : tabT.lookup msig.1 <;> simp [sT, hfl]
    rw [hfinT]
    dsimp only [blsBankWordFinish, caller]
    rw [hab]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hsel := blsBankSelectSample_eq (P.G₀.order d) msig.1 samples stW tabT countT hrem htab
    have hc : sW.coin = sT.1 := congrArg Prod.fst hsel
    have hre : (sW.exponent : ZMod (P.G₀.order d)) = sT.2 := congrArg Prod.snd hsel
    change (P.decode₀ d (if sW.coin then _ else _)).getD 0 = _
    rw [hc]
    cases sT.1 with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, P.decode₀_encode, Option.getD_some]
    | true =>
      simp only [↓reduceIte]
      have hsigW : (if P.isElem₀ (d, msig.2) then msig.2 else P.G₀.encode d 0) =
          P.G₀.encode d ((P.decode₀ d msig.2).getD (0 : P.G₀.Carrier d)) :=
        (P.toDecodableG₀.encode_decode_getD d msig.2 (0 : P.G₀.Carrier d)).symm
      rw [hsigW, P.G₀.smul_encode, ZMod.natCast_sub_mod_eq_neg, hre, neg_smul, P.G₀.add_encode,
        ← sub_eq_add_neg, P.decode₀_encode]
      rfl

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
    rw [show PFunctor.FreeM.bind (OracleComp.query (spec := RawWordSpec) q) cont =
      (OracleComp.query (spec := RawWordSpec) q >>= cont) from rfl]
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
  intro K digestEnc A samplesW samplesT caller prog wRun tRun
  have hsamplesT :
      samplesW.map (fun s : BLSBankSample => (s.coin, (s.exponent : ZMod (P.G₀.order d)))) =
        samplesT := by
    simp only [samplesW, samplesT, List.map_ofFn, Function.comp_def]
  have hstep := P.blsWordBankStep_eq_blsBankedReductionStep d (α • P.G₀.generator d)
    (α • P.G₁.generator d) (β • P.G₀.generator d) s n samplesW prog [] [] false 0 rfl
  simp only [List.drop_zero, hsamplesT] at hstep
  obtain ⟨h1, h2, h3, h4⟩ := hstep
  have ht : tRun = (Prod.map id (fun sigWord => (P.decode₀ d sigWord).getD 0) wRun.1,
      (OracleComp.interpret
        (P.toPairingGroupFamily.blsBankedReductionStep d (α • P.G₀.generator d)
          (β • P.G₀.generator d) samplesT)
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun msg => P.G₀.encode d <$> OracleComp.query (Sum.inl msg))
            (fun q => OracleComp.query (Sum.inr q)))
          (OracleComp.interpret (fun request => wordQuery digestEnc request.1 request.2)
            prog))).run ([], false, 0) |>.2) := by
    dsimp only [tRun, A, blsDecodedForger, savedCoinForger]
    rw [savedWordReplay_eq_interpret, OracleComp.interpret_map, StateT.run_map]
    dsimp only [Functor.map, Id.run]
    exact Prod.ext
      (congrArg (Prod.map id fun sigWord => (P.decode₀ d sigWord).getD 0) h1.symm) rfl
  rw [ht]
  have hfin := P.blsWordBankFinish_eq d (α • P.G₀.generator d) (α • P.G₁.generator d)
    (β • P.G₀.generator d) s n samplesW wRun.1 wRun.2 _ h2 h3 h4
  simpa only [hsamplesT, Prod.map, id_eq] using hfin

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
    refine PMF.bind_congr_on_support _ _ _ fun α _ =>
      PMF.bind_congr_on_support _ _ _ fun β _ =>
        PMF.bind_congr_on_support _ _ _ fun s _ =>
          PMF.bind_congr_on_support _ _ _ fun cs _ =>
            PMF.bind_congr_on_support _ _ _ fun rhosN _ => ?_
    have hzip :
        ((List.ofFn cs).zip (List.ofFn rhosN)).map (fun p => (⟨p.1, p.2⟩ : BLSBankSample)) =
          List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample) :=
      List.ext_getElem
        (by simp only [List.length_map, List.length_zip, List.length_ofFn, min_self, budget, K])
        fun i _ _ => by simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    rw [hzip, ProbOracleComp.eval_runState, savedWordReplay_eq_interpret]
    simp only [ProbComp.eval_pure, Prod.mk.eta]
    have hrun := runWith_pure_interpret_rawWordSpec
      (blsBankWordHandler P.toPairingGroupFamily
        ⟨n, d, P.G₀.encode d (α • P.G₀.generator d), P.G₁.encode d (α • P.G₁.generator d),
          P.G₀.encode d (β • P.G₀.generator d), s,
          List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)⟩)
      (savedWordReplay machine (fun op word => OracleComp.query (spec := RawWordSpec) (op, word))
        c e keyC keyD (n, P.G₁.encode d (α • P.G₁.generator d), s))
      ⟨[], false, List.ofFn fun i : Fin K => (⟨cs i, rhosN i⟩ : BLSBankSample)⟩
    dsimp only [blsBankWordHandler] at hrun
    rw [hrun, PMF.pure_bind]
    exact congrArg (fun z => PMF.pure (decide (z = (α * β) • P.G₀.generator d)))
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
  obtain ⟨keyC, keyD, hkeyBound⟩ := polynomiallyBounded_iff_le.mp
    (show PolynomiallyBounded fun n => c₁ * (c₂ * (n + 1) ^ k₂ + 1) ^ k₁ by fun_prop)
  have hgen : ∀ n keys,
      keys ∈ (ProbComp.eval (P.G₁.toFamily.schnorrSigKeyGen n (description n))).support →
        keys.1.length ≤ keyC * (n + 1) ^ keyD := by
    intro n keys hkeys
    rw [PrimeOrderGroupFamily.eval_schnorrSigKeyGen, PMF.mem_support_map_iff] at hkeys
    dsimp only [PrimeOrderGroupFamily.Companion.toFamily] at hkeys
    obtain ⟨α, _, rfl⟩ := hkeys
    exact (hlen₁ (description n) (α • P.G₁.generator (description n))).trans
      ((Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.succ_le_succ (hlen₂ n)) k₁)).trans
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
  have hK : PolynomiallyBounded K := by fun_prop
  have hKdiv : Negligible (fun n => (K n : ℝ≥0) / 2 ^ n) :=
    Negligible.polynomiallyBounded_div hK negligible_inv_two_pow
  have hsum : Negligible (fun n =>
      ((3 * (2 * (budget n + 1)) : ℕ) : ℝ≥0) *
        (Game.succProbability
          (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) +
          (K n : ℝ≥0) / 2 ^ n) + (1 : ℝ≥0) / 2 ^ n) :=
    ((hbreak.add hKdiv).polynomiallyBounded_mul (by fun_prop)).add negligible_one_div_two_pow
  refine negligible_of_le hsum fun n => ?_
  let d := description n
  let digestEnc : P.G₀.Carrier d ↪ List Bool := ⟨P.G₀.encode d, P.G₀.encode_injective d⟩
  let Aword := savedCoinForger machine digestEnc c e keyC keyD n
  obtain ⟨hcb, heqGame⟩ := hgame n (P.G₀.Carrier d) digestEnc (P.blsNativeROMScheme n d) rfl
  rw [heqGame, ← NNReal.coe_le_coe]
  let A := blsDecodedForger P d Aword
  let coin := ProbComp.eval (ProbComp.sampleDyadicCoin (budget n) 1)
  have hcoin : (coin true).toReal = (dyadicSize (budget n) : ℝ)⁻¹ := by
    simp [coin, ProbComp.eval_sampleDyadicCoin_true_toReal,
      Nat.min_eq_right (dyadicSize_pos (budget n)), one_div]
  have hcoron := P.toPairingGroupFamily.succProbability_eufCmaGame_blsTypedROMScheme_le_of_banked
    d A (P.callBounded_blsDecodedForger d hcb) coin hcoin
    (by exact_mod_cast lt_dyadicSize (budget n))
  have hadv := Game.coe_succProbability_le_add_of_advantage_le
    (NNReal.coe_le_coe.mpr ((Game.advantage_comm _ _).trans_le
      (P.coCdhGame_blsBankedCoCDHAdversary_le description machine c e keyC keyD n)))
  have hdy : (dyadicSize (budget n) : ℝ) ≤ (2 * (budget n + 1) : ℕ) := by
    exact_mod_cast dyadicSize_le (budget n)
  push_cast at hadv ⊢
  calc (Game.succProbability (eufCmaGame (P.blsNativeROMScheme n d) Aword) : ℝ)
      ≤ (Game.succProbability (eufCmaGame (P.toPairingGroupFamily.blsTypedROMScheme d) A) : ℝ) +
          1 / 2 ^ n := P.succProbability_eufCmaGame_blsNativeROMScheme_le n d Aword
    _ ≤ 2.72 * (dyadicSize (budget n) : ℝ) *
          (Game.succProbability (do
            let α ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
            let β ← PMF.uniformOfFintype (ZMod (P.G₀.order d))
            let z ← P.toPairingGroupFamily.blsBankedReduction d A (K n) coin
              (α • P.G₀.generator d) (α • P.G₁.generator d) (β • P.G₀.generator d)
            return decide (z = (α * β) • P.G₀.generator d)) : ℝ) + 1 / 2 ^ n := by gcongr
    _ ≤ 2.72 * (dyadicSize (budget n) : ℝ) *
          ((Game.succProbability
            (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
            (K n : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
        have hK_eq : (budget n : ℝ) + (budget n : ℝ) + 1 = (K n : ℝ) := by simp [K]
        rw [hK_eq] at hadv
        exact add_le_add (mul_le_mul_of_nonneg_left hadv (by positivity)) le_rfl
    _ ≤ 3 * ((2 * (budget n + 1) : ℕ) : ℝ) *
          ((Game.succProbability
            (P.G₀.coCdhGame P.G₁ (fun m => PMF.pure (description m)) adv n) : ℝ) +
            (K n : ℝ) / 2 ^ n) + 1 / 2 ^ n := by
              gcongr
              norm_num
    _ = _ := by push_cast; ring

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
