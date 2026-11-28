/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Pairing.BLSSecurity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT
import CslibFrontierTests.Crypto.PrimeFieldGroups
import CslibFrontierTests.Crypto.PrimeOrderGroupFixture
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum.Prime

/-!
# BLS signatures and pairing-assumption clients

An ordinary `module` client of `CslibFrontier.Crypto.Computational.Pairing.BLS`,
`CslibFrontier.Crypto.Computational.Pairing.BLSSecurity`, and
`CslibFrontier.Crypto.Computational.Pairing.Assumptions`:

1. **Decodable pairing fixture:** constructs `primeDecodableFields`
   (`DecodablePrimeOrderGroupFamily`) and `primeDecodablePairing` (`DecodablePairingGroupFamily`)
   over the additive groups `ZMod p` of prime order from
   `CslibFrontierTests.Crypto.PrimeFieldGroups`.
2. **Word/native BLS execution and encoding boundaries:** exercises `blsWordSign`, `blsWordVerify`,
   prefix-bounded hash reads, rejection of non-canonical bit encodings (`[true, false]`) and
   out-of-range residues (`Nat.bits 8` modulo `7`), `blsNativeROMScheme_unique_of_canonical`, and
   `wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame`.
3. **Banked reduction boundaries:** exercises `blsBankedReductionStep` and
   `blsBankedReductionFinish` both on an aborting signing-query collision (`coin = true` marks
   `aborted = true` and yields `0`) and on an unqueried `coin = true` hash forgery
   (`msig.2 - rhostar • u₀ = (α * β) • g₀`).
4. **Adaptive native forger and Bertrand-prime instantiation:** certifies an adaptive `IsOraclePPT`
   forger and instantiates both `CoCDH.eufCma_blsNativeROMScheme` and
   `CoCDH.sufCma_blsNativeROMScheme` on Bertrand primes `2 ^ n < p ≤ 2 ^ (n + 1)`
   ([BonehShoup2023], Theorem 15.1, pp. 627–629; noting that `CoCDH` fails on `ZMod p`).
5. **Nonvacuity witnesses:** proves `not_coCdh_const` and `not_decisionBDH_const`, showing both
   assumptions fail for every constant fixed-group setup law `fun _ => PMF.pure d`.
-/

set_option linter.privateModule false

noncomputable section

namespace CslibFrontierTests.Crypto.BLSSignature

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily
open Cslib.Crypto.PairingGroupFamily Cslib.Crypto.DecodablePairingGroupFamily
open Cslib.Crypto.Protocols Cslib.Crypto.Protocols.ROMSignature Turing.MultiTapeTM
open CslibFrontierTests.Crypto.PrimeFieldGroups CslibFrontierTests.Crypto.PrimeOrderGroupFixture
open scoped ENNReal NNReal

/-! ### Decodable pairing fixture over `primeFields` -/

/-- Canonical decoder for `primeFields`: accepts `w` iff it equals the canonical binary encoding of
its reduced residue modulo `p.1`. -/
private def primeDecode (p : PrimeDesc) (w : List Bool) : Option (ZMod p.val) :=
  if w == ((ofBits w % p.val).bits) then some (ofBits w : ZMod p.val) else none

private theorem primeDecode_encode (p : PrimeDesc) (x : ZMod p.val) :
    primeDecode p (primeFields.encode p x) = some x := by
  have : NeZero p.val := ⟨p.property.ne_zero⟩
  have hxlt : x.val < p.val := ZMod.val_lt x
  simp only [primeDecode, ofBits_bits, Nat.mod_eq_of_lt hxlt, beq_self_eq_true,
    ↓reduceIte, ZMod.natCast_zmod_val]

private theorem primeEncode_eq_of_decode_eq_some {p : PrimeDesc} {w : List Bool} {x : ZMod p.val}
    (h : primeDecode p w = some x) : w = primeFields.encode p x := by
  have : NeZero p.val := ⟨p.property.ne_zero⟩
  simp only [primeDecode] at h
  split at h
  · rename_i heq
    rw [Option.some.injEq] at h
    have hw : w = (ofBits w % p.val).bits := beq_iff_eq.mp heq
    have hval : x.val = ofBits w % p.val := by
      rw [← h, ZMod.val_natCast]
    simpa only [primeFields, hval] using hw
  · cases h

private theorem computableInPolyTime_primeIsElem :
    ComputableInPolyTime (fun p : PrimeDesc × List Bool => (primeDecode p.1 p.2).isSome)
      (encPair encPrime encBits) encBool := by
  have h1 : ComputableInPolyTime (fun p : PrimeDesc × List Bool => p.1)
      (encPair encPrime encBits) encPrime := by fun_prop
  have h2 : ComputableInPolyTime (fun p : PrimeDesc × List Bool => p.2)
      (encPair encPrime encBits) encBits := by fun_prop
  have hmodBits :
      ComputableInPolyTime (fun p : PrimeDesc × List Bool => ((ofBits p.2 % p.1.val).bits))
        (encPair encPrime encBits) encBits :=
    ((Decoder.nat.computableInPolyTime.comp h2).binary_mod'
      (computableInPolyTime_val.comp h1)).encoding_comp
  refine (h2.beq hmodBits).of_enc_eq fun p => ?_
  dsimp only [primeDecode]
  cases hbeq : p.2 == ((ofBits p.2 % p.1.val).bits) <;> simp

/-- `primeFields` equipped with its canonical bit-string decoder and polynomial-time membership
test. -/
private abbrev primeDecodableFields : DecodablePrimeOrderGroupFamily where
  toPrimeOrderGroupFamily := primeFields
  decode := primeDecode
  decode_encode := primeDecode_encode
  encode_eq_of_decode_eq_some := primeEncode_eq_of_decode_eq_some
  computableInPolyTime_isElem := computableInPolyTime_primeIsElem

private def primePairEncoded : PrimeDesc × List Bool × List Bool → List Bool
  | (p, x, y) => ((ofBits x * ofBits y) % p.val).bits

/-- Symmetric decodable pairing family over `ZMod p` (`G₀ = G₁ = GT = ZMod p` with generator `1`
and pairing `(u, v) ↦ u * v`). -/
private abbrev primeDecodablePairing : DecodablePairingGroupFamily :=
  DecodablePairingGroupFamily.ofDecodable primeDecodableFields primeFields.self primeFields.self
    (fun d => LinearMap.mul (ZMod d.val) (ZMod d.val))
    (fun _ => by simp [primeDecodableFields, primeFields, self])
    primePairEncoded
    (fun p u v => by
      have : NeZero p.val := ⟨p.property.ne_zero⟩
      simp [primePairEncoded, primeFields, self, primeDecodableFields, ofBits_bits, ZMod.val_mul])
    (by
      have hp := ComputableInPolyTime.id' (encIn := encDescBitsPair encPrime)
      exact (ComputableInPolyTime.binary_mod'
        (ComputableInPolyTime.binary_mul'
          (Decoder.nat.computableInPolyTime.comp hp.snd'.fst')
          (Decoder.nat.computableInPolyTime.comp hp.snd'.snd'))
        (computableInPolyTime_val.comp hp.fst')).encoding_comp)

/-! ### Word/native BLS execution and non-canonical encoding boundaries -/

private abbrev d7 : PrimeDesc := ⟨7, by norm_num⟩

private def fixedReply (answer : List Bool) :
    Unit × List Bool → StateT (List (List Bool)) PMF (List Bool) :=
  fun query log => PMF.pure (answer, query.2 :: log)

private theorem runWordSign_fixed (d : primeDecodablePairing.G₀.Desc) (limit : ℕ)
    (sk msg answer : List Bool) (log : List (List Bool)) :
    ProbOracleComp.runWith (fixedReply answer)
        (primeDecodablePairing.blsWordSign d limit sk msg) log =
      PMF.pure (primeDecodablePairing.G₀.smul (d, ofBits sk, answer.take limit), msg :: log) := by
  simp [blsWordSign, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, fixedReply,
    PMF.pure_map]

private theorem runWordVerify_fixed (d : primeDecodablePairing.G₀.Desc) (limit : ℕ)
    (pk msg sig answer : List Bool) (log : List (List Bool)) :
    ProbOracleComp.runWith (fixedReply answer)
        (primeDecodablePairing.blsWordVerify d limit pk msg sig) log =
      PMF.pure (primeDecodablePairing.isElem₀ (d, sig) &&
        decide (primeDecodablePairing.pairEncoded (d, answer.take limit, pk) =
          primeDecodablePairing.pairEncoded
            (d, sig, primeDecodablePairing.G₁.encode d (primeDecodablePairing.G₁.generator d))),
        msg :: log) := by
  simp [blsWordVerify, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, fixedReply,
    PMF.pure_map]

-- On `d7`, with secret scalar `5` (pk `Nat.bits 5`) and digest `Nat.bits 3 = [true, true]`,
-- signing produces `5 * 3 = 15 ≡ 1 (mod 7)`, whose canonical encoding is `[true]`, and verification
-- accepts it.
example :
    ProbOracleComp.runWith (fixedReply (Nat.bits 3))
      (primeDecodablePairing.blsWordSign d7 4 (Nat.bits 5) [true]) [] =
      PMF.pure ([true], [[true]]) := by
  rw [runWordSign_fixed]
  have htake : List.take 4 (Nat.bits 3) = primeDecodablePairing.G₀.encode d7 (3 : ZMod 7) := by
    decide
  rw [htake, ofBits_bits, primeDecodablePairing.G₀.smul_encode]
  have h15 : ((5 : ℕ) : ZMod 7) • (3 : ZMod 7) = (1 : ZMod 7) := by decide
  rw [h15]
  rfl

example :
    ProbOracleComp.runWith (fixedReply (Nat.bits 3))
      (primeDecodablePairing.blsWordVerify d7 4 (Nat.bits 5) [true] [true]) [] =
      PMF.pure (true, [[true]]) := by
  rw [runWordVerify_fixed]
  congr 1

-- Overlong RO replies are truncated to `limit = 3` bits: `[true, true, false, true]` has 3-bit
-- prefix `[true, true, false]` (`ofBits = 3`), so the signature `[true]` still verifies.
example :
    ProbOracleComp.runWith (fixedReply [true, true, false, true])
      (primeDecodablePairing.blsWordVerify d7 3 (Nat.bits 5) [true] [true]) [] =
      PMF.pure (true, [[true]]) := by
  rw [runWordVerify_fixed]
  congr 1

-- Non-canonical encoding boundary: `[true, false]` has `ofBits [true, false] = 1`, so its encoded
-- pairing matches the public key pairing on `Nat.bits 5` and `Nat.bits 3`, yet `blsWordVerify`
-- rejects it because `isElem₀ (d7, [true, false]) = false`.
example :
    primeDecodablePairing.pairEncoded (d7, Nat.bits 3, Nat.bits 5) =
      primeDecodablePairing.pairEncoded
        (d7, [true, false],
          primeDecodablePairing.G₁.encode d7 (primeDecodablePairing.G₁.generator d7)) ∧
    ProbOracleComp.runWith (fixedReply (Nat.bits 3))
      (primeDecodablePairing.blsWordVerify d7 4 (Nat.bits 5) [true] [true, false]) [] =
      PMF.pure (false, [[true]]) := by
  constructor
  · decide
  · rw [runWordVerify_fixed]
    congr 1

-- Oversized residue boundary: `Nat.bits 8` (`8 ≡ 1 mod 7`) satisfies the pairing equation modulo
-- `7` yet is rejected by `blsWordVerify` because `8 ∉ [0, 7)`.
example :
    ProbOracleComp.runWith (fixedReply (Nat.bits 3))
      (primeDecodablePairing.blsWordVerify d7 4 (Nat.bits 5) [true] (Nat.bits 8)) [] =
      PMF.pure (false, [[true]]) := by
  rw [runWordVerify_fixed]
  congr 1

-- Concrete uniqueness and SUF-CMA = EUF-CMA game equality for `primeDecodablePairing`.
example (n : ℕ) (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) :
    wordSufCmaGame
        ⟨primeDecodablePairing.G₀.encode d7, primeDecodablePairing.G₀.encode_injective d7⟩
        (primeDecodablePairing.blsNativeROMScheme n d7) forger =
      wordEufCmaGame
        ⟨primeDecodablePairing.G₀.encode d7, primeDecodablePairing.G₀.encode_injective d7⟩
        (primeDecodablePairing.blsNativeROMScheme n d7) forger :=
  primeDecodablePairing.wordSufCmaGame_blsNativeROMScheme_eq_wordEufCmaGame n d7 forger

/-! ### Banked Coron reduction boundary checks -/

-- Forgery win case (`α = 2, β = 3` on `d7`, target `(α * β) • 1 = 6`): signing `"s"` draws
-- `(false, 4)` (replying `4 • u₀ = 1` without aborting), hashing `"f"` draws `(true, 5)` (replying
-- `v₀ + 5 • 1 = 1`), and forgiving `("f", 2 • 1 = 2)` extracts `2 - 5 • u₀ = 2 - 3 = 6`.
example :
    let u₀ : primeDecodablePairing.G₀.Carrier d7 := 2
    let v₀ : primeDecodablePairing.G₀.Carrier d7 := 3
    let samples : List (Bool × ZMod (primeDecodablePairing.G₀.order d7)) := [(false, 4), (true, 5)]
    let prog : OracleComp (ForgerSpec (List Bool) (List Bool)
        (primeDecodablePairing.G₀.Carrier d7) (primeDecodablePairing.G₀.Carrier d7))
        (List Bool × primeDecodablePairing.G₀.Carrier d7) := do
      let _ ← OracleComp.query (Sum.inl [false])
      let h ← OracleComp.query (Sum.inr [true])
      return ([true], (2 : ZMod 7) • h)
    let res :=
      (OracleComp.interpret
        (primeDecodablePairing.toPairingGroupFamily.blsBankedReductionStep d7 u₀ v₀ samples)
        prog).run ([], false, 0)
    primeDecodablePairing.toPairingGroupFamily.blsBankedReductionFinish d7 u₀ samples res.1 res.2 =
      (6 : ZMod 7) := by
  decide

-- Abort case: if a signing query hits a `coin = true` sample, `blsBankedReductionStep` sets
-- `aborted = true` and `blsBankedReductionFinish` returns `0` even if a valid signature is output.
example :
    let u₀ : primeDecodablePairing.G₀.Carrier d7 := 2
    let v₀ : primeDecodablePairing.G₀.Carrier d7 := 3
    let samples : List (Bool × ZMod (primeDecodablePairing.G₀.order d7)) := [(true, 4), (true, 5)]
    let prog : OracleComp (ForgerSpec (List Bool) (List Bool)
        (primeDecodablePairing.G₀.Carrier d7) (primeDecodablePairing.G₀.Carrier d7))
        (List Bool × primeDecodablePairing.G₀.Carrier d7) := do
      let _ ← OracleComp.query (Sum.inl [false])
      let h ← OracleComp.query (Sum.inr [true])
      return ([true], (2 : ZMod 7) • h)
    let res :=
      (OracleComp.interpret
        (primeDecodablePairing.toPairingGroupFamily.blsBankedReductionStep d7 u₀ v₀ samples)
        prog).run ([], false, 0)
    res.2.2.1 = true ∧
      primeDecodablePairing.toPairingGroupFamily.blsBankedReductionFinish
        d7 u₀ samples res.1 res.2 = (0 : ZMod 7) := by
  decide

/-! ### Native `IsOraclePPT` forger and Bertrand-prime asymptotic instantiation -/

/-- Adaptive native forger: requests one signature on `[]`, queries the random oracle on that reply,
and returns a candidate forgery pair. -/
private def nativeForger (_ : ℕ) (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) := do
  let sig ← List.take 1 <$> ProbOracleComp.query (false, [])
  let digest ← List.take 3 <$> ProbOracleComp.query (true, sig)
  return (digest, sig)

private theorem nativeForger_ppt : IsOraclePPT (encPair encBits encBits) nativeForger := by
  unfold IsOraclePPT nativeForger
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  fun_prop

private theorem exists_bertrandPrime (n : ℕ) : ∃ p, p.Prime ∧ 2 ^ n < p ∧ p ≤ 2 * 2 ^ n :=
  Nat.exists_prime_lt_and_le_two_mul (2 ^ n) (pow_ne_zero n two_ne_zero)

private def bertrandPrime (n : ℕ) : primeDecodablePairing.G₀.Desc :=
  ⟨(exists_bertrandPrime n).choose, (exists_bertrandPrime n).choose_spec.1⟩

private theorem polynomiallyBounded_bertrandPrime :
    PolynomiallyBounded fun n => (primeDecodablePairing.G₀.encDesc (bertrandPrime n)).length := by
  refine PolynomiallyBounded.of_forall_le 2 1 fun n => ?_
  change (exists_bertrandPrime n).choose.bits.length ≤ _
  have hle := (exists_bertrandPrime n).choose_spec.2.2
  have hsize : (exists_bertrandPrime n).choose.size ≤ n + 2 := by
    apply Nat.size_le.mpr
    have hpos := Nat.two_pow_pos n
    rw [pow_succ, pow_succ]
    omega
  rw [Nat.size_eq_bits_len, pow_one]
  omega

private instance instFintypePrimeCarrier (p : PrimeDesc) :
    Fintype (primeDecodablePairing.G₀.Carrier p) :=
  @ZMod.fintype p.val ⟨p.property.ne_zero⟩

-- Discharging parameter bounds with Bertrand primes leaves only the co-CDH assumption for
-- `[BonehShoup2023]` Theorem 15.1 (which itself fails on `primeFields`, so this checks consistency
-- of the asymptotic `EUFCMA` and `SUFCMA` endpoints and their application to `nativeForger`).
example
    (hCoCDH : primeDecodablePairing.G₀.CoCDH primeDecodablePairing.G₁
      fun n => PMF.pure (bertrandPrime n)) :
    ROMSignature.EUFCMA
        (fun n => ⟨primeDecodablePairing.G₀.encode (bertrandPrime n),
          primeDecodablePairing.G₀.encode_injective _⟩)
        (fun n => primeDecodablePairing.blsNativeROMScheme n (bertrandPrime n)) ∧
      ROMSignature.SUFCMA
        (fun n => ⟨primeDecodablePairing.G₀.encode (bertrandPrime n),
          primeDecodablePairing.G₀.encode_injective _⟩)
        (fun n => primeDecodablePairing.blsNativeROMScheme n (bertrandPrime n)) :=
  ⟨CoCDH.eufCma_blsNativeROMScheme primeDecodablePairing hCoCDH polynomiallyBounded_bertrandPrime,
   CoCDH.sufCma_blsNativeROMScheme primeDecodablePairing hCoCDH polynomiallyBounded_bertrandPrime⟩

example
    (hCoCDH : primeDecodablePairing.G₀.CoCDH primeDecodablePairing.G₁
      fun n => PMF.pure (bertrandPrime n)) :
    Negligible fun n => Game.succProbability (wordSufCmaGame
      ⟨primeDecodablePairing.G₀.encode (bertrandPrime n),
        primeDecodablePairing.G₀.encode_injective _⟩
      (primeDecodablePairing.blsNativeROMScheme n (bertrandPrime n)) (nativeForger n)) :=
  (CoCDH.sufCma_blsNativeROMScheme primeDecodablePairing hCoCDH
    polynomiallyBounded_bertrandPrime).negligible nativeForger nativeForger_ppt

/-! ### Nonvacuity of `PrimeOrderGroupFamily.CoCDH` and `PairingGroupFamily.DecisionBDH` -/

/-- **Co-CDH fails for every fixed group and companion**, since `CoCDH` implies `DiscreteLog` and
guessing `0` succeeds with constant probability `1 / q`. -/
theorem not_coCdh_const (F : PrimeOrderGroupFamily) (C : F.Companion) (d : F.Desc) :
    ¬ F.CoCDH C fun _ => PMF.pure d := by
  intro hCoCDH
  have hneg := hCoCDH.discreteLog (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

/-- Accept when both the first challenge `u₀ ∈ G₀` and the target challenge `z ∈ GT` are the
group identity `0`. -/
private def dbdhIdentityTest (P : PairingGroupFamily) : P.DBDHDistinguisher :=
  fun _ _ u₀ _ _ _ z => pure (decide (u₀ = 0) && decide (z = 0))

private theorem dbdhIdentityTest_isPPT (P : PairingGroupFamily) :
    (dbdhIdentityTest P).IsPPT := by
  have hid : ComputableInPolyTime id P.encDBDHInput P.encDBDHInput :=
    ComputableInPolyTime.id'
  have hd : ComputableInPolyTime (fun x : P.DBDHInput => x.groupParameters)
      P.encDBDHInput P.G₀.encDesc :=
    P.encDBDHInput_groupParameters_polyTime hid
  have hlz : ComputableInPolyTime (fun x : P.DBDHInput => P.G₀.encode x.groupParameters x.leftZero)
      P.encDBDHInput encBits :=
    P.encDBDHInput_leftZero_polyTime hid
  have hct :
      ComputableInPolyTime
        (fun x : P.DBDHInput => P.GT.encode x.groupParameters x.candidateTarget)
        P.encDBDHInput encBits :=
    P.encDBDHInput_candidateTarget_polyTime hid
  have hz₀ : ComputableInPolyTime (fun x : P.DBDHInput => P.G₀.encode x.groupParameters 0)
      P.encDBDHInput encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero hd
  have hzT : ComputableInPolyTime (fun x : P.DBDHInput => P.GT.encode x.groupParameters 0)
      P.encDBDHInput encBits :=
    PrimeOrderGroupFamily.Companion.computableInPolyTime_encode_zero
      (C := P.GT) (d := fun x : P.DBDHInput => x.groupParameters) hd
  refine (hlz.beq hz₀ |>.bool_and' (hct.beq hzT)).isPPTOn.congr fun x => ?_
  simp only [dbdhIdentityTest, ProbComp.eval_pure, Bool.beq_eq_decide_eq,
    (P.G₀.encode_injective _).eq_iff, (P.GT.encode_injective _).eq_iff]

private theorem succProbability_dbdhRealGame_dbdhIdentityTest (P : PairingGroupFamily)
    (d : P.G₀.Desc) (n : ℕ) :
    Game.succProbability (P.dbdhRealGame (fun _ => PMF.pure d) (dbdhIdentityTest P) n) =
      (P.G₀.order d : ℝ≥0)⁻¹ := by
  simp only [dbdhRealGame, Game.withSetup_pure, eval_dbdhRealExperiment, dbdhIdentityTest,
    ProbComp.eval_pure, smul_eq_zero, P.G₀.generator_ne_zero, P.GT.toFamily.generator_ne_zero,
    or_false, ← Bool.decide_and]
  have hcond : ∀ (α β γ : ZMod (P.G₀.order d)),
      decide (α = 0 ∧ α * β * γ = 0) = decide (α = 0) := by
    intro α β γ
    exact decide_eq_decide.mpr (and_iff_left_of_imp fun ha => by simp [ha])
  simp only [hcond, PMF.bind_const]
  rw [Game.succProbability, PMF.bind_pure_decide_eq_apply_true', PMF.uniformOfFintype_apply,
    ZMod.card, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

private theorem succProbability_dbdhRandomGame_dbdhIdentityTest (P : PairingGroupFamily)
    (d : P.G₀.Desc) (n : ℕ) :
    Game.succProbability (P.dbdhRandomGame (fun _ => PMF.pure d) (dbdhIdentityTest P) n) =
      (P.G₀.order d : ℝ≥0)⁻¹ ^ 2 := by
  simp only [dbdhRandomGame, Game.withSetup_pure, eval_dbdhRandomExperiment, dbdhIdentityTest,
    ProbComp.eval_pure, smul_eq_zero, P.G₀.generator_ne_zero, P.GT.toFamily.generator_ne_zero,
    or_false, PMF.bind_const]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    Finset.sum_ite_eq', sq]

/-- **Decision BDH fails for every fixed pairing group**, since `dbdhIdentityTest` distinguishes
real tuples from random tuples with constant advantage `1 / q - 1 / q²`. -/
theorem not_decisionBDH_const (P : PairingGroupFamily) (d : P.G₀.Desc) :
    ¬ P.DecisionBDH fun _ => PMF.pure d := by
  intro hDBDH
  have hneg := hDBDH (dbdhIdentityTest P) (dbdhIdentityTest_isPPT P)
  simp only [Game.advantage, succProbability_dbdhRealGame_dbdhIdentityTest,
    succProbability_dbdhRandomGame_dbdhIdentityTest] at hneg
  refine not_negligible_const ?_ hneg
  rw [ne_eq, nndist_eq_zero]
  intro heq
  have hq : (2 : ℝ) ≤ P.G₀.order d := by exact_mod_cast (P.G₀.prime_order d).two_le
  have hr : ((P.G₀.order d : ℝ))⁻¹ = ((P.G₀.order d : ℝ))⁻¹ ^ 2 := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  field_simp at hr
  nlinarith

end CslibFrontierTests.Crypto.BLSSignature
