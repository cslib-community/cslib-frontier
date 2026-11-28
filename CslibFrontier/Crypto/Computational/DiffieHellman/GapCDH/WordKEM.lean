/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.GapCDH.Assumption
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.Product
public import Mathlib.Data.FinEnum
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime

/-!
# Word-level random-oracle DH-KEM and certified Gap-CDH reduction

Over a `DecodablePrimeOrderGroupFamily`, this module states the word-level random-oracle Diffie–
Hellman key-encapsulation mechanism ([KatzLindell2020], Construction 12.19, p. 431) and its
word-level ROM IND-CCA security notion ([KatzLindell2020], Definition 12.13, p. 425), together with
the explicit word-level Gap-CDH reduction `dhKEMToGapCDHWord` of Theorem 12.22 (p. 435) and its
uniform strict oracle-PPT certificate `isOraclePPTOn_dhKEMToGapCDHWord`.

On decapsulation of a candidate ciphertext word `c`, `dhKEMDecapsWord` validates group membership
via `F.decode d c` (`F.isElem`) and rejects words outside `Set.range (F.encode d)` with `none`,
following the ciphertext-validation remark of [KatzLindell2020], Construction 12.23 (pp. 435–436).
In `dhKEMCCAWordGame`, the random oracle `H : F.Carrier d → BitString (keyLen n)` is drawn
uniformly, hash queries outside `Set.range (F.encode d)` return `[]`, and decapsulation refuses
both `c = cStar` and `¬ F.isElem (d, c)` with `encOption encBits none = []`.

`dhKEMToGapCDHWord` mirrors `PrimeOrderGroupFamily.dhKEMToGapCDH` on words: when the public key
word equals `F.encode d 0` it outputs `F.encode d 0`; otherwise it samples a uniform `keyLen n`-bit
challenge key, answers the KEM adversary's `hash` and `decaps` queries from a list of
`DHKEMSimEntry` records using `F.isElem` and `queryDDHWord`, and extracts the first hash entry `z`
satisfying `queryDDHWord cStar z`. Its oracle-PPT certificate uses only `IsOraclePPT encBool A` and
`ComputableInPolyTime keyLen encUnary encUnary`.

## Main definitions

* `Cslib.Crypto.DHKEMOp`, `Cslib.Crypto.DHKEMChallenge`, `Cslib.Crypto.encDHKEMChallenge`: oracle
  operations and encoded challenge input `(d, h, c⋆, k̂)` of a word-level ROM IND-CCA adversary.
* `Cslib.Crypto.DHKEMSimEntry`, `Cslib.Crypto.encDHKEMSimEntry`: query-table entry record and
  encoding for the word reduction's `List.findSomeM?` scans.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMEncapsWord`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMDecapsWord`: word-level encapsulation and
  membership-validating decapsulation of Construction 12.19.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMCCAWordAnswer`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMCCAWordGame`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DHKEMROMINDCCA`: word-level ROM IND-CCA oracle,
  experiment, and asymptotic security definition.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.simWordHandler`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.extractDHWord`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMToGapCDHWord`: word-level query simulator,
  table extractor, and Gap-CDH reduction.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMDecapsWord_encapsWord`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.dhKEMDecapsWord_of_not_isElem`: decapsulation
  recovers honest keys and rejects malformed ciphertexts.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.isOraclePPTOn_dhKEMToGapCDHWord`: uniform strict
  oracle-PPT certificate for `dhKEMToGapCDHWord`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], 3rd edition,
  Definition 12.13 (p. 425), Construction 12.19 (p. 431), §12.4.4 (p. 434), Theorem 12.22
  (p. 435), and Construction 12.23 (pp. 435–436).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Oracle operations of a word-level ROM IND-CCA adversary against Construction 12.19: random-
oracle hash queries (`hash`) and decapsulation queries (`decaps`). -/
inductive DHKEMOp where
  /-- Evaluate the random oracle `H` at a candidate group-element word. -/
  | hash
  /-- Decapsulate a candidate ciphertext word. -/
  | decaps
  deriving DecidableEq

instance : FinEnum DHKEMOp := FinEnum.ofList [.hash, .decaps] (by intro x; cases x <;> simp)

instance : Finite DHKEMOp :=
  Finite.of_injective (fun | .hash => false | .decaps => true) (by rintro (_ | _) (_ | _) <;> simp)

/-- Challenge input `(d, h, c⋆, k̂)` of a word-level ROM IND-CCA adversary against Construction
12.19 ([KatzLindell2020], Definition 12.13, p. 425, and Construction 12.19, p. 431). -/
structure DHKEMChallenge (F : PrimeOrderGroupFamily) where
  /-- Public parameters selecting the group, its prime order, and its generator. -/
  groupParameters : F.Desc
  /-- Encoded public key element (`F.encode d (x • g)` in the experiment). -/
  publicPoint : List Bool
  /-- Encoded challenge ciphertext (`F.encode d (y • g)` in the experiment). -/
  ciphertext : List Bool
  /-- Challenge symmetric key word (`kReal` or uniform `kRand` of length `keyLen n`). -/
  key : List Bool

/-- Encoding of `DHKEMChallenge F` as the framed tuple of its four fields. -/
enc_structure encDHKEMChallenge (F : PrimeOrderGroupFamily) : DHKEMChallenge F where
  groupParameters : F.encDesc, publicPoint : encBits, ciphertext : encBits, key : encBits

/-- One entry in the word-level reduction's query table: `isDecaps = false` records a random-oracle
query `elem = z`, and `isDecaps = true` records a decapsulation query `elem = c`, paired with the
sampled `key` returned for it. -/
structure DHKEMSimEntry where
  /-- `false` for a hash entry (`.inl z`), `true` for a decapsulation entry (`.inr c`). -/
  isDecaps : Bool
  /-- Encoded group element (`z` or `c`). -/
  elem : List Bool
  /-- Key word returned for this entry. -/
  key : List Bool
  deriving DecidableEq

/-- Encoding of `DHKEMSimEntry` as the framed triple `(isDecaps, elem, key)`. -/
enc_structure encDHKEMSimEntry : DHKEMSimEntry where
  isDecaps : encBool, elem : encBits, key : encBits

/-- Match a table entry against a hash query `z`: hash entries compare `e.elem == z`, while
decapsulation entries ask the external DDH oracle whether `z = x • e.elem`. -/
def hashSelectWord (z : List Bool) (e : DHKEMSimEntry) :
    WordOracleComp Unit (Option (List Bool)) :=
  if e.isDecaps then
    (fun b => if b then some e.key else none) <$> queryDDHWord e.elem z
  else
    pure (if e.elem == z then some e.key else none)

/-- Match a table entry against a decapsulation query `c`: decapsulation entries compare
`e.elem == c`, while hash entries ask the external DDH oracle whether `e.elem = x • c`. -/
def decapsSelectWord (c : List Bool) (e : DHKEMSimEntry) :
    WordOracleComp Unit (Option (List Bool)) :=
  if e.isDecaps then
    pure (if e.elem == c then some e.key else none)
  else
    (fun b => if b then some e.key else none) <$> queryDDHWord c e.elem

/-- Return the key of the first matching entry in `table`, or sample a fresh uniform `m`-bit key
and prepend `⟨isDecaps, elem, key⟩`. -/
noncomputable def simLookupWord (m : ℕ)
    (select : DHKEMSimEntry → WordOracleComp Unit (Option (List Bool)))
    (isDecaps : Bool) (elem : List Bool) (table : List DHKEMSimEntry) :
    WordOracleComp Unit (List Bool × List DHKEMSimEntry) := do
  match ← table.findSomeM? select with
  | some key => return (key, table)
  | none =>
    let key ← ProbOracleComp.sample (BitString.sampleList m)
    return (key, ⟨isDecaps, elem, key⟩ :: table)

/-- Test whether a table entry is a hash entry `z` satisfying `z = x • cStar`. -/
def extractSelectWord (cStar : List Bool) (e : DHKEMSimEntry) :
    WordOracleComp Unit (Option (List Bool)) :=
  if e.isDecaps then
    pure none
  else
    (fun b => if b then some e.elem else none) <$> queryDDHWord cStar e.elem

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

/-- Canonical `Fintype` instance on `F.Carrier d` induced by the bijection
`α ↦ α • F.generator d` from `ZMod (F.order d)`. -/
@[instance_reducible]
noncomputable def fintypeCarrier (d : F.Desc) : Fintype (F.Carrier d) :=
  Fintype.ofBijective _ (F.toPrimeOrderGroupFamily.smul_generator_bijective d)

/-- Output of word-level DH-KEM encapsulation: encoded group-element ciphertext and key word. -/
structure DHKEMEncapsOutput where
  /-- Encoded ciphertext `F.encode d (y • g)`. -/
  ciphertext : List Bool
  /-- Encapsulated symmetric key word `List.ofFn (H (y • h))`. -/
  key : List Bool
  deriving DecidableEq

/-- Word-level encapsulation of [KatzLindell2020], Construction 12.19 (p. 431), for random oracle
`H`, public key element `h`, and ephemeral exponent `y`: outputs the encoded ciphertext
`F.encode d (y • g)` and the key word `List.ofFn (H (y • h))`. -/
def dhKEMEncapsWord (d : F.Desc) {m : ℕ} (H : F.Carrier d → BitString m) (h : F.Carrier d)
    (y : ZMod (F.order d)) : DHKEMEncapsOutput :=
  ⟨F.encode d (y • F.generator d), List.ofFn (H (y • h))⟩

/-- Word-level decapsulation of [KatzLindell2020], Construction 12.19 (p. 431), with explicit group
membership validation ([KatzLindell2020], Construction 12.23, pp. 435–436): decodes `ciphertext` via
`F.decode d` and returns `some (List.ofFn (H (x • c)))` on valid group encodings, or `none` when
`¬ F.isElem (d, ciphertext)`. -/
def dhKEMDecapsWord (d : F.Desc) {m : ℕ} (H : F.Carrier d → BitString m) (x : ZMod (F.order d))
    (ciphertext : List Bool) : Option (List Bool) :=
  (F.decode d ciphertext).map fun c => List.ofFn (H (x • c))

/-- Decapsulating an honestly generated encapsulation under the matching secret key recovers its
symmetric key word. -/
@[simp] theorem dhKEMDecapsWord_encapsWord (d : F.Desc) {m : ℕ} (H : F.Carrier d → BitString m)
    (x y : ZMod (F.order d)) :
    F.dhKEMDecapsWord d H x (F.dhKEMEncapsWord d H (x • F.generator d) y).ciphertext =
      some (F.dhKEMEncapsWord d H (x • F.generator d) y).key := by
  simp [dhKEMDecapsWord, dhKEMEncapsWord, F.decode_encode, smul_smul, mul_comm]

/-- Decapsulation rejects any candidate ciphertext word outside `Set.range (F.encode d)`. -/
theorem dhKEMDecapsWord_of_not_isElem (d : F.Desc) {m : ℕ} (H : F.Carrier d → BitString m)
    (x : ZMod (F.order d)) {ciphertext : List Bool} (hc : F.isElem (d, ciphertext) = false) :
    F.dhKEMDecapsWord d H x ciphertext = none := by
  have hnone : F.decode d ciphertext = none :=
    F.decode_eq_none_iff.mpr ((F.isElem_eq_false_iff d ciphertext).mp hc)
  simp [dhKEMDecapsWord, hnone]

/-- Word-level ROM IND-CCA oracle answer for Construction 12.19: `.hash w` evaluates `H` when
`F.decode d w = some z` and returns `[]` otherwise; `.decaps c` refuses `c = cStar` with `[]`
(`encOption encBits none`) and otherwise encodes `F.dhKEMDecapsWord d H x c` via
`encOption encBits`. -/
def dhKEMCCAWordAnswer (d : F.Desc) {m : ℕ} (H : F.Carrier d → BitString m)
    (x : ZMod (F.order d)) (cStar : List Bool) : DHKEMOp × List Bool → List Bool
  | (.hash, w) =>
    match F.decode d w with
    | some z => List.ofFn (H z)
    | none => []
  | (.decaps, c) =>
    if c = cStar then []
    else encOption encBits (F.dhKEMDecapsWord d H x c)

/-- Fixed-group word-level ROM IND-CCA game for Construction 12.19 at parameter `n` and group `d`:
`bit = true` supplies the real encapsulated key (`b = 0` in [KatzLindell2020], Definition 12.13,
p. 425) and `bit = false` supplies an independent uniform `keyLen n`-bit key (`b = 1`). -/
noncomputable def dhKEMCCAWordGameAt (keyLen : ℕ → ℕ)
    (adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool) (bit : Bool) (n : ℕ)
    (d : F.Desc) : Game :=
  letI : Fintype (F.Carrier d) := F.fintypeCarrier d
  do
    let x ← PMF.uniformOfFintype (ZMod (F.order d))
    let y ← PMF.uniformOfFintype (ZMod (F.order d))
    let H ← Probability.PMF.pi fun _ : F.Carrier d =>
      ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))
    let random ← ProbComp.eval (ProbComp.uniform (BitString (keyLen n)))
    let ⟨cStar, kReal⟩ := F.dhKEMEncapsWord d H (x • F.generator d) y
    let challenge := encDHKEMChallenge F.toPrimeOrderGroupFamily
      ⟨d, F.encode d (x • F.generator d), cStar, if bit then kReal else List.ofFn random⟩
    ProbComp.eval ((adversary n challenge).run
      fun req => pure (F.dhKEMCCAWordAnswer d H x cStar req))

/-- **Word-level ROM IND-CCA game** for Construction 12.19 ([KatzLindell2020], Definition 12.13,
p. 425, and Construction 12.19, p. 431) over `setup` and symmetric key length `keyLen`. -/
noncomputable def dhKEMCCAWordGame (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool) (bit : Bool) (n : ℕ) : Game :=
  (setup n).bind (F.dhKEMCCAWordGameAt keyLen adversary bit n)

/-- **Random-oracle IND-CCA security** of the word-level DH-KEM (Construction 12.19) with key
length `keyLen`: every uniform strict oracle-PPT adversary has negligible distinguishing advantage
between the real-key (`bit = true`) and random-key (`bit = false`) worlds.

This notion is DH-KEM-specific and local to this module, pending the generic KEM records of the
crypto readability program (#4817, I3 #4894). -/
def DHKEMROMINDCCA (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ) : Prop :=
  Game.Indistinguishable
    (fun A n => F.dhKEMCCAWordGame setup keyLen A true n)
    (fun A n => F.dhKEMCCAWordGame setup keyLen A false n)
    (IsOraclePPT encBool)

/-- Stateful query simulator of `dhKEMToGapCDHWord` at parameter `n`, group `d`, and challenge
ciphertext word `cStar`: answers valid `.hash z` and non-challenge valid `.decaps c` queries
consistently from its `DHKEMSimEntry` table via `queryDDHWord`, and answers out-of-group or
challenge-decapsulation queries with `[]` without modifying the table. -/
noncomputable def simWordHandler (keyLen : ℕ → ℕ) (n : ℕ) (d : F.Desc) (cStar : List Bool)
    (req : DHKEMOp × List Bool) (table : List DHKEMSimEntry) :
    WordOracleComp Unit (List Bool × List DHKEMSimEntry) :=
  match req with
  | (.hash, z) =>
    if F.isElem (d, z) then
      simLookupWord (keyLen n) (hashSelectWord z) false z table
    else
      pure ([], table)
  | (.decaps, c) =>
    if !F.isElem (d, c) || c == cStar then
      pure ([], table)
    else
      (fun (key, nextTable) => (encOption encBits (some key), nextTable)) <$>
        simLookupWord (keyLen n) (decapsSelectWord c) true c table

/-- Extract the first hash entry `z` in `table` satisfying `queryDDHWord cStar z`, falling back to
`F.encode d 0` when none matches. -/
def extractDHWord (d : F.Desc) (cStar : List Bool) (table : List DHKEMSimEntry) :
    WordOracleComp Unit (List Bool) :=
  (fun r => r.getD (F.encode d 0)) <$> table.findSomeM? (extractSelectWord cStar)

/-- **Word-level Gap-CDH reduction** of [KatzLindell2020], Theorem 12.22 (p. 435), mirroring
`PrimeOrderGroupFamily.dhKEMToGapCDH`: on `input = ⟨n, d, cStar, h⟩`, outputs `F.encode d 0` when
`h == F.encode d 0`; otherwise samples a uniform `keyLen n`-bit challenge key, runs `adversary n`
against `simWordHandler`, and extracts the first hash query matching `x • cStar` via
`extractDHWord`. -/
noncomputable def dhKEMToGapCDHWord (keyLen : ℕ → ℕ)
    (adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool) : F.GapCDHAdversary :=
  fun input =>
    if input.rightPublic == F.encode input.groupParameters 0 then
      pure (F.encode input.groupParameters 0)
    else do
      let key ← ProbOracleComp.sample (BitString.sampleList (keyLen input.secParam))
      let challenge := encDHKEMChallenge F.toPrimeOrderGroupFamily
        ⟨input.groupParameters, input.rightPublic, input.leftPublic, key⟩
      let (_, finalTable) ← (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (F.simWordHandler keyLen input.secParam input.groupParameters input.leftPublic))
        (adversary input.secParam challenge)).run []
      F.extractDHWord input.groupParameters input.leftPublic finalTable

/-! ### Uniform strict oracle-PPT certificate for `dhKEMToGapCDHWord` -/

end DecodablePrimeOrderGroupFamily

private structure SearchState where
  remaining : List DHKEMSimEntry
  found : Option (List Bool)

private enc_structure encSearchState : SearchState where
  remaining : (encList encDHKEMSimEntry), found : (encOption encBits)

private def searchStep {α : Type}
    (select : α → DHKEMSimEntry → WordOracleComp Unit (Option (List Bool))) (a : α)
    (s : SearchState) : WordOracleComp Unit SearchState :=
  if s.found.isSome || s.remaining.isEmpty then
    pure ⟨[], s.found⟩
  else
    let e := s.remaining.headD ⟨false, [], []⟩
    (fun r => if r.isSome then SearchState.mk [] r else ⟨s.remaining.tail, none⟩) <$> select a e

private theorem iterate_searchStep_eq_findSomeM? {α : Type}
    (select : α → DHKEMSimEntry → WordOracleComp Unit (Option (List Bool))) (a : α)
    (t : List DHKEMSimEntry) :
    SearchState.found <$> OracleComp.iterate t.length (searchStep select a) ⟨t, none⟩ =
      t.findSomeM? (select a) := by
  induction t with
  | nil => simp [List.findSomeM?_nil]
  | cons e rest ih =>
    rw [List.length_cons, OracleComp.iterate_succ_bind]
    simp only [searchStep, Option.isSome_none, List.isEmpty_cons, Bool.or_false, Bool.false_eq_true,
      ↓reduceIte, List.headD_cons, List.tail_cons, List.findSomeM?_cons, map_bind, bind_map_left]
    refine congrArg (Bind.bind (select a e)) (funext fun r => ?_)
    cases r with
    | none => simpa using ih
    | some v =>
      have hpure : searchStep select a ⟨[], some v⟩ = pure ⟨[], some v⟩ := by simp [searchStep]
      simp [OracleComp.iterate_eq_pure rest.length _ _ hpure]

-- Dedicated bounded-iteration certificate rather than `IsOraclePPTOn.foldlM_of_bounded_growth`,
-- which requires constant step growth whereas `Option (List Bool)` grows by up to `keyLen n` bits.
private theorem isOraclePPTOn_findSomeM? {α : Type} {input : α ↪ List Bool}
    {table : α → List DHKEMSimEntry}
    {select : α → DHKEMSimEntry → WordOracleComp Unit (Option (List Bool))}
    (htable : ComputableInPolyTime table input (encList encDHKEMSimEntry))
    (hselect : IsOraclePPTOn (encPair input encDHKEMSimEntry) (encOption encBits)
      (fun p => select p.1 p.2))
    (hval : ∀ a e v, some v ∈ OracleComp.support (select a e) →
      v.length ≤ e.elem.length + e.key.length) :
    IsOraclePPTOn input (encOption encBits)
      (fun a => (table a).findSomeM? (select a)) := by
  have hisEmpty : ComputableInPolyTime
      (fun p : α × SearchState => p.2.remaining.isEmpty)
      (encPair input encSearchState) encBool :=
    (ComputableInPolyTime.listIsEmpty' encDHKEMSimEntry).comp
      (by polytime)
  have hcond : ComputableInPolyTime
      (fun p : α × SearchState => p.2.found.isSome || p.2.remaining.isEmpty)
      (encPair input encSearchState) encBool := by polytime
  have hyes : IsOraclePPTOn (encPair input encSearchState) encSearchState
      (fun p => pure ⟨[], p.2.found⟩) :=
    ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime)
  have hprep : ComputableInPolyTime
      (fun p : α × SearchState => (p.1, p.2.remaining.headD ⟨false, [], []⟩))
      (encPair input encSearchState) (encPair input encDHKEMSimEntry) := by polytime
  have htail : ComputableInPolyTime
      (fun q : (α × SearchState) × Option (List Bool) => q.1.2.remaining.tail)
      (encPair (encPair input encSearchState) (encOption encBits))
      (encList encDHKEMSimEntry) :=
    (ComputableInPolyTime.listTail encDHKEMSimEntry).comp
      (by polytime)
  have hpost : ComputableInPolyTime
      (fun q : (α × SearchState) × Option (List Bool) =>
        if q.2.isSome then SearchState.mk [] q.2 else ⟨q.1.2.remaining.tail, none⟩)
      (encPair (encPair input encSearchState) (encOption encBits)) encSearchState := by polytime
  have hno : IsOraclePPTOn (encPair input encSearchState) encSearchState
      (fun p =>
        (fun r => if r.isSome then SearchState.mk [] r else ⟨p.2.remaining.tail, none⟩) <$>
          select p.1 (p.2.remaining.headD ⟨false, [], []⟩)) :=
    (hselect.preprocess hprep).map_with hpost
  have hstep : IsOraclePPTOn (encPair input encSearchState) encSearchState
      (fun p => searchStep select p.1 p.2) :=
    IsOraclePPTOn.cond hcond hyes hno
  have hloop : IsOraclePPTOn input encSearchState
      (fun a => OracleComp.iterate (table a).length (searchStep select a) ⟨table a, none⟩) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth
      (hcount := by polytime) (hinitial := by polytime) hstep (PolyBounded.const 0) ?_
    intro a s next hnext
    simp only [searchStep, OracleComp.support] at hnext
    by_cases hc : (s.found.isSome || s.remaining.isEmpty) = true
    · simp only [hc, ↓reduceIte, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hnext
      subst hnext
      enc_len [encSearchState_apply]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, OracleComp.mem_supportWith_map_iff] at hnext
      obtain ⟨r, hr, hnext⟩ := hnext
      subst hnext
      obtain ⟨hf, hne⟩ : s.found = none ∧ s.remaining ≠ [] := by
        cases h1 : s.found <;> cases h2 : s.remaining <;> simp_all
      cases hrem : s.remaining with
      | nil => exact absurd hrem hne
      | cons e rest =>
        cases r with
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
          enc_len [encSearchState_apply, hrem, hf]
        | some v =>
          have hv := hval a e v (by simpa [OracleComp.support, hrem] using hr)
          simp only [Option.isSome_some, ↓reduceIte]
          enc_len [encSearchState_apply, encDHKEMSimEntry_apply, hrem, hf]
  refine (IsOraclePPTOn.map hloop (f := SearchState.found)
      (encSearchState_found_polyTime ComputableInPolyTime.id')).congr fun a State oracle s => ?_
  rw [iterate_searchStep_eq_findSomeM?]

theorem mem_support_findSomeM?
    {select : DHKEMSimEntry → WordOracleComp Unit (Option (List Bool))}
    {table : List DHKEMSimEntry} {v : List Bool}
    (h : some v ∈ OracleComp.support (table.findSomeM? select)) :
    ∃ e ∈ table, some v ∈ OracleComp.support (select e) := by
  induction table with
  | nil => simp [List.findSomeM?_nil, OracleComp.support] at h
  | cons e rest ih =>
    simp only [List.findSomeM?_cons, OracleComp.support, OracleComp.mem_supportWith_bind_iff] at h
    obtain ⟨r, hr, h'⟩ := h
    cases r with
    | some w =>
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff, Option.some.injEq] at h'
      exact ⟨e, List.mem_cons_self, h' ▸ hr⟩
    | none =>
      obtain ⟨e', he', hse'⟩ := ih h'
      exact ⟨e', List.mem_cons_of_mem e he', hse'⟩

private structure ReductionCaller (F : PrimeOrderGroupFamily) where
  input : GapCDHInput F
  key : List Bool

private enc_structure encReductionCaller (F : PrimeOrderGroupFamily) : ReductionCaller F where
  input : (encGapCDHInput F), key : encBits

private structure SimCall (F : PrimeOrderGroupFamily) where
  caller : ReductionCaller F
  op : DHKEMOp
  word : List Bool
  table : List DHKEMSimEntry

private enc_structure encSimCall (F : PrimeOrderGroupFamily) : SimCall F where
  caller : (encReductionCaller F), op : (encFinEnum DHKEMOp), word : encBits,
  table : (encList encDHKEMSimEntry)

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

private theorem isOraclePPTOn_simLookup {select : SimCall F.toPrimeOrderGroupFamily →
      DHKEMSimEntry → WordOracleComp Unit (Option (List Bool))}
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (isDecaps : Bool)
    (hselect : IsOraclePPTOn (encPair (encSimCall F.toPrimeOrderGroupFamily) encDHKEMSimEntry)
      (encOption encBits) (fun p => select p.1 p.2))
    (hval : ∀ c e v, some v ∈ OracleComp.support (select c e) →
      v.length ≤ e.elem.length + e.key.length) :
    IsOraclePPTOn (encSimCall F.toPrimeOrderGroupFamily)
      (encPair encBits (encList encDHKEMSimEntry))
      (fun c => simLookupWord (keyLen c.caller.input.secParam) (select c) isDecaps c.word c.table)
    := by
  have hfind := isOraclePPTOn_findSomeM? (table := SimCall.table) (by polytime) hselect hval
  have hm : ComputableInPolyTime
      (fun p : SimCall F.toPrimeOrderGroupFamily × Option (List Bool) =>
        keyLen p.1.caller.input.secParam)
      (encPair (encSimCall F.toPrimeOrderGroupFamily) (encOption encBits)) encUnary :=
    hkeyLen.comp (by polytime)
  have hhit : IsOraclePPTOn
      (encPair (encSimCall F.toPrimeOrderGroupFamily) (encOption encBits))
      (encPair encBits (encList encDHKEMSimEntry))
      (fun p => pure (p.2.getD [], p.1.table)) :=
    ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime)
  have hmiss : IsOraclePPTOn (Operation := Unit)
      (encPair (encSimCall F.toPrimeOrderGroupFamily) (encOption encBits))
      (encPair encBits (encList encDHKEMSimEntry))
      (fun p =>
        (fun key => (key, DHKEMSimEntry.mk isDecaps p.1.word key :: p.1.table)) <$>
          ProbOracleComp.sample (BitString.sampleList (keyLen p.1.caller.input.secParam))) :=
    (hm.sampleList.isOraclePPTOn (Operation := Unit)).map_with
      (f := fun p key => (key, DHKEMSimEntry.mk isDecaps p.1.word key :: p.1.table))
      (by polytime)
  have hcont : IsOraclePPTOn (Operation := Unit)
      (encPair (encSimCall F.toPrimeOrderGroupFamily) (encOption encBits))
      (encPair encBits (encList encDHKEMSimEntry))
      (fun p => match p.2 with
        | some key => pure (key, p.1.table)
        | none => do
          let key ← ProbOracleComp.sample (BitString.sampleList (keyLen p.1.caller.input.secParam))
          return (key, ⟨isDecaps, p.1.word, key⟩ :: p.1.table)) := by
    refine (IsOraclePPTOn.cond (condition := fun p => p.2.isSome) (by polytime) hhit hmiss).congr
      fun p State oracle s => ?_
    cases p.2 <;> simp [bind_pure_comp]
  exact hfind.bind_with hcont

private theorem dhkem_eq_key_of_mem_support_select {w : List Bool} {e : DHKEMSimEntry}
    {v : List Bool}
    (h : some v ∈ OracleComp.support (hashSelectWord w e) ∨
      some v ∈ OracleComp.support (decapsSelectWord w e)) : v = e.key := by
  have hpure {b : Bool} (hv : some v ∈ OracleComp.support
      (pure (if b then some e.key else none) : WordOracleComp Unit (Option (List Bool)))) :
      v = e.key := by
    simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hv
    split_ifs at hv
    exact Option.some.inj hv
  have hmap {q : WordOracleComp Unit Bool}
      (hv : some v ∈ OracleComp.support ((fun b => if b then some e.key else none) <$> q)) :
      v = e.key := by
    simp only [OracleComp.support, OracleComp.mem_supportWith_map_iff] at hv
    obtain ⟨(_ | _), _, hb⟩ := hv
    · simp at hb
    · exact Option.some.inj hb.symm
  rcases h with h | h <;> by_cases hd : e.isDecaps <;>
    simp only [hashSelectWord, decapsSelectWord, hd, Bool.false_eq_true, ↓reduceIte] at h
  · exact hmap h
  · exact hpure h
  · exact hpure h
  · exact hmap h

private theorem isOraclePPTOn_simWordHandler {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn
      (encHandlerCall (encReductionCaller F.toPrimeOrderGroupFamily) (encFinEnum DHKEMOp)
        (encList encDHKEMSimEntry))
      (encPair encBits (encList encDHKEMSimEntry))
      (fun call => F.simWordHandler keyLen call.1.input.secParam
        call.1.input.groupParameters call.1.input.leftPublic call.2.1 call.2.2) := by
  have hhashSel : IsOraclePPTOn (encPair (encSimCall F.toPrimeOrderGroupFamily) encDHKEMSimEntry)
      (encOption encBits) (fun p => hashSelectWord p.1.word p.2) := by
    refine IsOraclePPTOn.cond (by polytime) ?_
      (ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime))
    exact (isOraclePPTOn_queryDDHWord (by polytime) (by polytime)).map_with (by polytime)
  have hdecSel : IsOraclePPTOn (encPair (encSimCall F.toPrimeOrderGroupFamily) encDHKEMSimEntry)
      (encOption encBits) (fun p => decapsSelectWord p.1.word p.2) := by
    refine IsOraclePPTOn.cond (by polytime)
      (ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime)) ?_
    exact (isOraclePPTOn_queryDDHWord (by polytime) (by polytime)).map_with (by polytime)
  have hhashLookup := F.isOraclePPTOn_simLookup (select := fun c e => hashSelectWord c.word e)
    hkeyLen false hhashSel fun _ _ _ hv =>
      dhkem_eq_key_of_mem_support_select (.inl hv) ▸ Nat.le_add_left _ _
  have hdecLookup := F.isOraclePPTOn_simLookup (select := fun c e => decapsSelectWord c.word e)
    hkeyLen true hdecSel fun _ _ _ hv =>
      dhkem_eq_key_of_mem_support_select (.inr hv) ▸ Nat.le_add_left _ _
  have hop : ComputableInPolyTime (SimCall.op (F := F.toPrimeOrderGroupFamily))
      (encSimCall F.toPrimeOrderGroupFamily) (encFinEnum DHKEMOp) :=
    encSimCall_op_polyTime F.toPrimeOrderGroupFamily ComputableInPolyTime.id'
  have hsimCall : IsOraclePPTOn (encSimCall F.toPrimeOrderGroupFamily)
      (encPair encBits (encList encDHKEMSimEntry))
      (fun c => F.simWordHandler keyLen c.caller.input.secParam c.caller.input.groupParameters
        c.caller.input.leftPublic (c.op, c.word) c.table) := by
    refine IsOraclePPTOn.finite_cases (Operation := Unit)
      (tagEncoding := encFinEnum DHKEMOp) (tag := SimCall.op)
      (branch := fun choice (c : SimCall F.toPrimeOrderGroupFamily) =>
        F.simWordHandler keyLen c.caller.input.secParam c.caller.input.groupParameters
          c.caller.input.leftPublic (choice, c.word) c.table)
      hop fun choice => ?_
    cases choice with
    | hash =>
      exact IsOraclePPTOn.cond (by polytime) hhashLookup
        (ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime))
    | decaps =>
      exact IsOraclePPTOn.cond (by polytime)
        (ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime))
        (IsOraclePPTOn.map hdecLookup (f := fun (key, nextTable) =>
          (encOption encBits (some key), nextTable)) (by polytime))
  exact hsimCall.preprocess
    (prepare := fun call : ReductionCaller F.toPrimeOrderGroupFamily ×
        (DHKEMOp × List Bool) × List DHKEMSimEntry =>
      SimCall.mk call.1 call.2.1.1 call.2.1.2 call.2.2) (by polytime)

private theorem simWordHandler_preserve (keyLen : ℕ → ℕ)
    (c : ReductionCaller F.toPrimeOrderGroupFamily) (req : DHKEMOp × List Bool)
    (table : List DHKEMSimEntry) (hinv : ∀ e ∈ table, e.key.length ≤ keyLen c.input.secParam)
    (res : List Bool × List DHKEMSimEntry)
    (hmem : res ∈ OracleComp.support
      (F.simWordHandler keyLen c.input.secParam c.input.groupParameters c.input.leftPublic
        req table)) :
    (∀ e ∈ res.2, e.key.length ≤ keyLen c.input.secParam) ∧
      res.1.length ≤ 4 * req.2.length + 2 * keyLen c.input.secParam + 16 ∧
      (encList encDHKEMSimEntry res.2).length ≤
        (encList encDHKEMSimEntry table).length +
          (4 * req.2.length + 2 * keyLen c.input.secParam + 16) := by
  obtain ⟨op, w⟩ := req
  obtain ⟨resKey, resTable⟩ := res
  dsimp only
  have hlookup (isDec : Bool) (select : DHKEMSimEntry → WordOracleComp Unit (Option (List Bool)))
      (hsel : ∀ e v, some v ∈ OracleComp.support (select e) → v = e.key)
      {key : List Bool} {t' : List DHKEMSimEntry}
      (hm : (key, t') ∈ OracleComp.support
        (simLookupWord (keyLen c.input.secParam) select isDec w table)) :
      (∀ e ∈ t', e.key.length ≤ keyLen c.input.secParam) ∧
        key.length ≤ keyLen c.input.secParam ∧
        (encList encDHKEMSimEntry t').length ≤
          (encList encDHKEMSimEntry table).length +
            (4 * w.length + 2 * keyLen c.input.secParam + 16) := by
    simp only [simLookupWord, OracleComp.support, OracleComp.mem_supportWith_bind_iff] at hm
    obtain ⟨found, hfound, hm⟩ := hm
    cases found with
    | some k =>
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨e, he, hse⟩ := mem_support_findSomeM? hfound
      exact ⟨hinv, hsel e _ hse ▸ hinv e he, by omega⟩
    | none =>
      have hm' : (key, t') ∈ OracleComp.support (do
          let k ← ProbOracleComp.sample (BitString.sampleList (keyLen c.input.secParam))
          pure (k, DHKEMSimEntry.mk isDec w k :: table)) := hm
      simp only [OracleComp.support, OracleComp.mem_supportWith_bind_iff,
        OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm'
      obtain ⟨_, hk, rfl, rfl⟩ := hm'
      have hks : key ∈ OracleComp.support
          (ProbOracleComp.sample (BitString.sampleList (keyLen c.input.secParam))) := hk
      have hlen : key.length = keyLen c.input.secParam := by
        simpa only [ProbOracleComp.support_sample, BitString.eval_sampleList,
          BitString.mem_support_uniformList_iff] using hks
      refine ⟨List.forall_mem_cons.mpr ⟨by simp [hlen], hinv⟩, hlen.le, ?_⟩
      enc_len [encDHKEMSimEntry_apply, hlen]
  cases op with
  | hash =>
    by_cases helem : F.isElem (c.input.groupParameters, w) = true
    · simp only [simWordHandler, helem, ↓reduceIte] at hmem
      obtain ⟨h1, h2, h3⟩ := hlookup false (hashSelectWord w)
        (fun _ _ hv => dhkem_eq_key_of_mem_support_select (.inl hv)) hmem
      exact ⟨h1, by omega, h3⟩
    · simp only [simWordHandler, helem, Bool.false_eq_true, ↓reduceIte, OracleComp.support,
        OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨hinv, by simp,
        by omega⟩
  | decaps =>
    by_cases hbad : (!F.isElem (c.input.groupParameters, w) ||
        w == c.input.leftPublic) = true
    · simp only [simWordHandler, hbad, ↓reduceIte, OracleComp.support,
        OracleComp.supportWith_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨hinv, by simp,
        by omega⟩
    · simp only [simWordHandler, hbad, Bool.false_eq_true, ↓reduceIte, OracleComp.support,
        OracleComp.mem_supportWith_map_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨key, t'⟩, hlk, rfl, rfl⟩ := hmem
      obtain ⟨h1, h2, h3⟩ := hlookup true (decapsSelectWord w)
        (fun _ _ hv => dhkem_eq_key_of_mem_support_select (.inr hv)) hlk
      exact ⟨h1, by simp [encOption]; omega, h3⟩

private theorem isOraclePPTOn_extractDHWord :
    IsOraclePPTOn
      (encPair (encReductionCaller F.toPrimeOrderGroupFamily)
        (encPair encBool (encList encDHKEMSimEntry)))
      encBits (fun p => F.extractDHWord p.1.input.groupParameters p.1.input.leftPublic p.2.2) := by
  have hextSel : IsOraclePPTOn
      (encPair (encPair (encReductionCaller F.toPrimeOrderGroupFamily)
        (encPair encBool (encList encDHKEMSimEntry))) encDHKEMSimEntry)
      (encOption encBits) (fun p => extractSelectWord p.1.1.input.leftPublic p.2) := by
    have hcs : ComputableInPolyTime
        (fun p : (ReductionCaller F.toPrimeOrderGroupFamily × Bool × List DHKEMSimEntry) ×
            DHKEMSimEntry => p.1.1.input.leftPublic)
        (encPair (encPair (encReductionCaller F.toPrimeOrderGroupFamily)
          (encPair encBool (encList encDHKEMSimEntry))) encDHKEMSimEntry) encBits := by polytime
    refine IsOraclePPTOn.cond (by polytime)
      (ComputableInPolyTime.isOraclePPTOn (Operation := Unit) (by polytime)) ?_
    exact (isOraclePPTOn_queryDDHWord hcs (by polytime)).map_with (by polytime)
  have hextFind := isOraclePPTOn_findSomeM?
    (select := fun p e => extractSelectWord p.1.input.leftPublic e)
    (table := fun p : ReductionCaller F.toPrimeOrderGroupFamily × Bool × List DHKEMSimEntry =>
      p.2.2) (by polytime) hextSel fun _ e v hv => by
      by_cases hd : e.isDecaps
      · simp [extractSelectWord, hd, OracleComp.support] at hv
      · simp only [extractSelectWord, hd, Bool.false_eq_true, ↓reduceIte, OracleComp.support,
          OracleComp.mem_supportWith_map_iff] at hv
        obtain ⟨b, _, hb⟩ := hv
        cases b <;> simp only [↓reduceIte, reduceCtorEq, Option.some.injEq] at hb
        exact hb ▸ Nat.le_add_right _ _
  have hgrp : ComputableInPolyTime
      (fun q : (ReductionCaller F.toPrimeOrderGroupFamily × Bool × List DHKEMSimEntry) ×
          Option (List Bool) => F.encode q.1.1.input.groupParameters 0)
      (encPair (encPair (encReductionCaller F.toPrimeOrderGroupFamily)
        (encPair encBool (encList encDHKEMSimEntry))) (encOption encBits)) encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero (by polytime)
  exact hextFind.map_with (by polytime)

/-- **Uniform strict oracle-PPT certificate** for `dhKEMToGapCDHWord`, derived solely from
`IsOraclePPT encBool adversary` and `ComputableInPolyTime keyLen encUnary encUnary`. -/
theorem isOraclePPTOn_dhKEMToGapCDHWord {keyLen : ℕ → ℕ}
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    (hA : IsOraclePPT encBool adversary)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits
      (F.dhKEMToGapCDHWord keyLen adversary) := by
  have hprepare : ComputableInPolyTime
      (fun c : ReductionCaller F.toPrimeOrderGroupFamily =>
        (c.input.secParam, encDHKEMChallenge F.toPrimeOrderGroupFamily
          ⟨c.input.groupParameters, c.input.rightPublic, c.input.leftPublic, c.key⟩))
      (encReductionCaller F.toPrimeOrderGroupFamily) (encPair encUnary encBits) := by polytime
  have hres : ComputableInPolyTime
      (fun p : ReductionCaller F.toPrimeOrderGroupFamily × List Bool =>
        4 * p.2.length + 2 * keyLen p.1.input.secParam + 16)
      (encPair (encReductionCaller F.toPrimeOrderGroupFamily) encBits) encUnary := by
    have hk : ComputableInPolyTime
        (fun p : ReductionCaller F.toPrimeOrderGroupFamily × List Bool =>
          keyLen p.1.input.secParam)
        (encPair (encReductionCaller F.toPrimeOrderGroupFamily) encBits) encUnary :=
      hkeyLen.comp (by polytime)
    polytime
  have hrun := hA.run_interpret_preprocess_open
    (handler := fun caller req table => F.simWordHandler keyLen caller.input.secParam
      caller.input.groupParameters caller.input.leftPublic req table)
    (resources := fun c w => 4 * w.length + 2 * keyLen c.input.secParam + 16)
    (stateEncoding := encList encDHKEMSimEntry) hprepare (F.isOraclePPTOn_simWordHandler hkeyLen)
    (initial := fun _ => ([] : List DHKEMSimEntry))
    (ComputableInPolyTime.const ([] : List DHKEMSimEntry))
    (fun c table => ∀ e ∈ table, e.key.length ≤ keyLen c.input.secParam) (by simp) hres
    (F.simWordHandler_preserve keyLen)
  have hsampleKey : IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits
      (fun input => ProbOracleComp.sample (BitString.sampleList (keyLen input.secParam))) :=
    ((hkeyLen.comp (by polytime)).sampleList).isOraclePPTOn (Operation := Unit)
  have hbody : IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits
      (fun input => do
        let key ← ProbOracleComp.sample (BitString.sampleList (keyLen input.secParam))
        let (_, finalTable) ← (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (F.simWordHandler keyLen input.secParam input.groupParameters input.leftPublic))
          (adversary input.secParam (encDHKEMChallenge F.toPrimeOrderGroupFamily
            ⟨input.groupParameters, input.rightPublic, input.leftPublic, key⟩))).run []
        F.extractDHWord input.groupParameters input.leftPublic finalTable) := by
    have hcaller := (hrun.bind_with
      (second := fun (c : ReductionCaller F.toPrimeOrderGroupFamily)
          ((_, finalTable) : Bool × List DHKEMSimEntry) =>
        F.extractDHWord c.input.groupParameters c.input.leftPublic finalTable)
      F.isOraclePPTOn_extractDHWord).preprocess
      (input := encPair (encGapCDHInput F.toPrimeOrderGroupFamily) encBits)
      (prepare := fun p : GapCDHInput F.toPrimeOrderGroupFamily × List Bool =>
        ReductionCaller.mk p.1 p.2) (by polytime)
    exact hsampleKey.bind_with hcaller
  have hzero : ComputableInPolyTime
      (fun input : GapCDHInput F.toPrimeOrderGroupFamily => F.encode input.groupParameters 0)
      (encGapCDHInput F.toPrimeOrderGroupFamily) encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero (by polytime)
  exact IsOraclePPTOn.cond (by polytime) (hzero.isOraclePPTOn (Operation := Unit)) hbody

/-- Specialization of `isOraclePPTOn_dhKEMToGapCDHWord` to `keyLen = id`. -/
theorem isOraclePPTOn_dhKEMToGapCDHWord_id
    {adversary : ℕ → List Bool → WordOracleComp DHKEMOp Bool}
    (hA : IsOraclePPT encBool adversary) :
    IsOraclePPTOn (encGapCDHInput F.toPrimeOrderGroupFamily) encBits
      (F.dhKEMToGapCDHWord id adversary) :=
  F.isOraclePPTOn_dhKEMToGapCDHWord hA ComputableInPolyTime.id'

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
