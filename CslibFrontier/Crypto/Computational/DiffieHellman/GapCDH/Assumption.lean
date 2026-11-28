/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Decodable
public import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# The asymptotic Gap-CDH assumption on decodable prime-order group families

For a `DecodablePrimeOrderGroupFamily`, the word-level gap computational Diffie–Hellman (Gap-CDH)
experiment ([KatzLindell2020], §12.4.4, p. 434) draws `d ← setup n` and independent uniform
exponents `a, b : ZMod (F.order d)`, gives the adversary the unary security parameter `n`, the
group description `d`, and the encoded elements `F.encode d (a • g)` and `F.encode d (b • g)`
(`GapCDHInput`), together with a word-level fixed-base decisional Diffie–Hellman oracle
`ddhWordOracle d b`, and accepts when the adversary outputs `F.encode d ((a * b) • g)`.

On a request word `w`, `ddhWordOracle d y` decodes `w` with `ddhOracleQueryDecoder` into candidate
words `(u, v)` and returns `encBool true` if and only if `w = encDDHOracleQuery ⟨u, v⟩`, both `u`
and `v` pass `F.isElem`, and their decoded group elements satisfy `V = y • U`; all non-canonical or
out-of-group queries return `encBool false`.

`DecodablePrimeOrderGroupFamily.GapCDH setup` states that every uniform strict oracle-PPT adversary
(`IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits`) wins `gapCDHWordGame` with
negligible probability. Because any closed PPT word-level CDH solver lifts to an oracle-free
Gap-CDH solver via `ProbOracleComp.sample`, `GapCDH` implies `WordCDH`, `CDH`, and `DiscreteLog`.

## Main definitions

* `Cslib.Crypto.DDHOracleQuery`, `Cslib.Crypto.encDDHOracleQuery`,
  `Cslib.Crypto.ddhOracleQueryDecoder`: framed pair of candidate element words `(U, V)` for
  word-level DDH queries and its total polynomial-time decoder.
* `Cslib.Crypto.GapCDHInput`, `Cslib.Crypto.encGapCDHInput`: encoded input `(1^n, d, u, v)` of a
  word-level Gap-CDH adversary.
* `Cslib.Crypto.queryDDHWord`: query the external word-level DDH oracle on `(u, v)` and read its
  1-bit Boolean answer.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.ddhOraclePred`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.ddhWordOracle`: the word-level fixed-base DDH
  predicate and oracle `O_y`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDHAdversary`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.gapCDHWordGame`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH`: word-level Gap-CDH adversaries, game, and
  asymptotic hardness assumption.

## Main results

* `Cslib.Crypto.isOraclePPTOn_queryDDHWord`: `queryDDHWord` preserves `IsOraclePPTOn`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.ddhOraclePred_encode`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.run_queryDDHWord`: on canonical group encodings,
  `queryDDHWord` agrees with the typed `ddhOracle` test `decide (V = y • U)`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH.wordCDH`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH.cdh`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.GapCDH.discreteLog`: `GapCDH` implies `WordCDH`,
  `CDH`, and `DiscreteLog`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], 3rd edition,
  §12.4.4, p. 434.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- A word-level fixed-base DDH oracle query `(U, V)`, asking whether `V = y • U` for the
challenger's hidden exponent `y`. -/
structure DDHOracleQuery where
  /-- Encoded candidate base element `U`. -/
  base : List Bool
  /-- Encoded candidate target element `V`. -/
  target : List Bool
  deriving DecidableEq

/-- Encoding of `DDHOracleQuery` as the framed pair of its two word fields. -/
enc_structure encDDHOracleQuery : DDHOracleQuery where
  base : encBits, target : encBits

/-- Total polynomial-time decoder for `encDDHOracleQuery`. -/
def ddhOracleQueryDecoder : Decoder encDDHOracleQuery :=
  (Decoder.bits.pair Decoder.bits).map
    (fun p => ⟨p.1, p.2⟩) (fun q => (q.base, q.target))
    (fun ⟨_, _⟩ => rfl) (fun _ => rfl)

/-- Input `(1^n, d, u, v)` of a word-level Gap-CDH adversary over `F`: unary security parameter,
group description `d`, and two candidate element words (`F.encode d (a • g)` and
`F.encode d (b • g)` in the experiment). -/
structure GapCDHInput (F : PrimeOrderGroupFamily) where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its prime order, and its generator. -/
  groupParameters : F.Desc
  /-- Encoded first public element (`F.encode d (a • g)` in the experiment). -/
  leftPublic : List Bool
  /-- Encoded second public element (`F.encode d (b • g)` in the experiment). -/
  rightPublic : List Bool

/-- Encoding of `GapCDHInput F`: unary `secParam`, `groupParameters` under `F.encDesc`, and the two
element words under `encBits`, framed as a nested pair. -/
enc_structure encGapCDHInput (F : PrimeOrderGroupFamily) : GapCDHInput F where
  secParam : encUnary, groupParameters : F.encDesc, leftPublic : encBits, rightPublic : encBits

/-- Query the external fixed-base DDH word oracle on candidate element words `(u, v)` and decode
its Boolean answer bit via `Decoder.bool`. -/
def queryDDHWord (u v : List Bool) : WordOracleComp Unit Bool :=
  Decoder.bool.decode <$> ProbOracleComp.query ((), encDDHOracleQuery ⟨u, v⟩)

/-- `queryDDHWord` is uniform strict oracle-PPT whenever its two word arguments are computable in
polynomial time: reading the first symbol of the reply requires only a 1-bit prefix
(`IsOraclePPTOn.query_take`
with limit `1`). -/
@[fun_prop]
theorem isOraclePPTOn_queryDDHWord {α : Type} {input : α ↪ List Bool} {u v : α → List Bool}
    (hu : ComputableInPolyTime u input encBits) (hv : ComputableInPolyTime v input encBits) :
    IsOraclePPTOn input encBool (fun a => queryDDHWord (u a) (v a)) := by
  have hreq := (encDDHOracleQuery_mk_polyTime hu hv).encoding_comp
  have htake : IsOraclePPTOn input encBits (fun a =>
      List.take 1 <$>
        ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
          ((), encDDHOracleQuery ⟨u a, v a⟩)) :=
    IsOraclePPTOn.query_take () hreq (ComputableInPolyTime.const 1)
  refine (IsOraclePPTOn.map htake Decoder.bool.computableInPolyTime).congr
    fun a State oracle s => ?_
  have hhead : ∀ w : List Bool, Decoder.bool.decode (List.take 1 w) = Decoder.bool.decode w := by
    intro w; cases w <;> rfl
  simp only [queryDDHWord, Functor.map_map, hhead]

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

/-- Word-level fixed-base DDH test on candidate element words `u` and `v`: `true` iff both `u` and
`v` are valid encodings in `F.Carrier d` and their decoded elements satisfy `V = y • U`. -/
def ddhOraclePred (d : F.Desc) (y : ZMod (F.order d)) (u v : List Bool) : Bool :=
  F.isElem (d, u) && F.isElem (d, v) && decide (F.decode d v = (F.decode d u).map (y • ·))

/-- On encoded group elements `U, V : F.Carrier d`, `ddhOraclePred` decides `V = y • U`. -/
@[simp] theorem ddhOraclePred_encode (d : F.Desc) (y : ZMod (F.order d)) (u v : F.Carrier d) :
    F.ddhOraclePred d y (F.encode d u) (F.encode d v) = decide (v = y • u) := by
  simp [ddhOraclePred, F.decode_encode]

/-- Characterization of `ddhOraclePred d y u v = true` in terms of `F.encode d`. -/
theorem ddhOraclePred_eq_true_iff (d : F.Desc) (y : ZMod (F.order d)) (u v : List Bool) :
    F.ddhOraclePred d y u v = true ↔
      ∃ U : F.Carrier d, u = F.encode d U ∧ v = F.encode d (y • U) := by
  constructor
  · intro h
    simp only [ddhOraclePred, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨U, hUdec, hUenc⟩ := F.exists_decode_eq_some_of_isElem h.1.1
    rw [hUdec, Option.map_some, F.decode_eq_some_iff] at h
    exact ⟨U, hUenc.symm, h.2⟩
  · rintro ⟨U, rfl, rfl⟩
    simp [ddhOraclePred_encode]

/-- Word-level fixed-base DDH oracle `O_y` ([KatzLindell2020], §12.4.4, p. 434): on a canonical
query word `encDDHOracleQuery ⟨u, v⟩`, returns `encBool (F.ddhOraclePred d y u v)`; non-canonical
words return `encBool false`. -/
def ddhWordOracle (d : F.Desc) (y : ZMod (F.order d)) (w : List Bool) : List Bool :=
  let q := ddhOracleQueryDecoder.decode w
  encBool (encDDHOracleQuery q == w && F.ddhOraclePred d y q.base q.target)

theorem ddhWordOracle_encDDHOracleQuery (d : F.Desc) (y : ZMod (F.order d))
    (u v : List Bool) :
    F.ddhWordOracle d y (encDDHOracleQuery ⟨u, v⟩) = encBool (F.ddhOraclePred d y u v) := by
  unfold ddhWordOracle
  rw [ddhOracleQueryDecoder.decode_enc]
  simp

@[simp] theorem run_queryDDHWord (d : F.Desc) (y : ZMod (F.order d)) (u v : List Bool) :
    (queryDDHWord u v).run (fun req => pure (F.ddhWordOracle d y req.2)) =
      pure (F.ddhOraclePred d y u v) := by
  simp only [queryDDHWord, ProbOracleComp.run_map, ProbOracleComp.run_query, map_pure,
    ddhWordOracle_encDDHOracleQuery, Decoder.bool.decode_enc]

/-- A word-level Gap-CDH adversary over `F` maps `GapCDHInput F.toPrimeOrderGroupFamily` to a
candidate word `List Bool`, with private coins and access to a single external word channel (`O_b`
in `gapCDHWordGame`). -/
abbrev GapCDHAdversary : Type :=
  GapCDHInput F.toPrimeOrderGroupFamily → WordOracleComp Unit (List Bool)

/-- The word-level Gap-CDH game ([KatzLindell2020], §12.4.4, p. 434): draw `d ← setup n` and
independent uniform `a, b : ZMod (F.order d)`, run `adversary` on
`⟨n, d, F.encode d (a • g), F.encode d (b • g)⟩` against `ddhWordOracle d b`, and accept when the
output word equals `F.encode d ((a * b) • g)`. -/
noncomputable def gapCDHWordGame (setup : ℕ → PMF F.Desc) (adversary : F.GapCDHAdversary)
    (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => do
    let a ← $ᵗ ZMod (F.order d)
    let b ← $ᵗ ZMod (F.order d)
    let guess ← (adversary
      ⟨n, d, F.encode d (a • F.generator d), F.encode d (b • F.generator d)⟩).run
      fun req => pure (F.ddhWordOracle d b req.2)
    return decide (guess = F.encode d ((a * b) • F.generator d))

/-- **The asymptotic Gap-CDH assumption** ([KatzLindell2020], §12.4.4, p. 434): every uniform
strict oracle-PPT adversary on `encGapCDHInput` wins `gapCDHWordGame` with negligible probability.

Deviations from [KatzLindell2020], §12.4.4, p. 434:
* The textbook states the gap-CDH problem informally (computing `g^{xy}` from `(g^x, g^y)` given
  oracle `O_y(U, V) = 1 ↔ V = U^y`) without a standalone numbered definition; here it is cast in
  the library's uniform strict oracle-PPT model (`IsOraclePPTOn`).
* Group parameters are drawn from an arbitrary `setup : ℕ → PMF F.Desc` rather than an efficient
  group generator `G(1^n)`, matching `DiscreteLog`, `CDH`, and `DDH`.
* Inputs, oracle queries, and outputs are bit strings; `ddhWordOracle` checks canonical pair
  framing and `F.isElem` membership, returning `encBool false` on malformed queries. -/
def GapCDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : F.GapCDHAdversary,
    IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits adversary →
      Negligible fun n => Game.succProbability (F.gapCDHWordGame setup adversary n)

/-- **`GapCDH` implies word-level `WordCDH`**: any closed PPT word-level CDH adversary lifts via
`ProbOracleComp.sample` to an oracle-PPT Gap-CDH adversary that makes no DDH queries and has the
exact same success probability. -/
theorem GapCDH.wordCDH {F : DecodablePrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.GapCDH setup) : F.toPrimeOrderGroupFamily.WordCDH setup := by
  intro adversary hA
  let lifted : F.GapCDHAdversary := fun x =>
    ProbOracleComp.sample
      (adversary x.secParam (x.groupParameters, x.leftPublic, x.rightPublic))
  have hprep : ComputableInPolyTime
      (fun x : GapCDHInput F.toPrimeOrderGroupFamily =>
        (x.secParam, x.groupParameters, x.leftPublic, x.rightPublic))
      (encGapCDHInput F.toPrimeOrderGroupFamily) F.toPrimeOrderGroupFamily.encWordCDHInput :=
    (ComputableInPolyTime.id' (encIn := encGapCDHInput F.toPrimeOrderGroupFamily)).of_enc_eq
      fun x => (encGapCDHInput_apply F.toPrimeOrderGroupFamily x).symm
  have hlifted : IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits lifted :=
    hA.isOraclePPTOn.preprocess hprep
  refine (h lifted hlifted).congr fun n => ?_
  simp only [gapCDHWordGame, PrimeOrderGroupFamily.cdhWordGame, lifted, ProbOracleComp.run_sample]

/-- **`GapCDH` implies `CDH`**. -/
theorem GapCDH.cdh {F : DecodablePrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.GapCDH setup) : F.toPrimeOrderGroupFamily.CDH setup :=
  h.wordCDH.cdh

/-- **`GapCDH` implies `DiscreteLog`**. -/
theorem GapCDH.discreteLog {F : DecodablePrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.GapCDH setup) : F.toPrimeOrderGroupFamily.DiscreteLog setup :=
  h.cdh.discreteLog

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
