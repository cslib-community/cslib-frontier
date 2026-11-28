/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Mathlib.Data.FinEnum
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Control.Monad.StateT
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PPT

/-!
# The certified IND-CPA reductions of the word-level Fujisaki–Okamoto families

The IND-CCA bounds of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot` and `…Bot`
reduce to the two-stage IND-CPA advantage of one explicit adversary,
`Scheme.romFilterCpaReduction`. This module gives that reduction for the word-level family
`WordPKE` of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word` as a chosen-message
adversary of `Encryption.gameOn`, and proves that it is uniform strict PPT whenever the adversary
it wraps is uniform strict oracle PPT.

**Adversaries.** A word-level ROM IND-CCA adversary is a program
`A : ℕ → List Bool → WordOracleComp CCAOp Bool`. At parameter `n` it receives the challenge word
`Encryption.encKEMChallenge (pk, k*, c*)`, the layout of the word-level KEM distinguishers of
`Encryption.KEMINDCPA`, and calls the oracles `G`, `H` and decapsulation (`CCAOp`). Its efficiency
is `IsOraclePPT encBool A`.

**The simulator.** `WordPKE.simFilterWordHandler d` answers the adversary without the secret key.
A request in the domain is answered by the typed keyless simulator `Scheme.simFilterHandler` of
the bundle `WordPKE.scheme P keyLen n`, on the same state `SimState`; a decapsulation answer is
encoded with `encOption encBits`. The domain is: messages of length `msgLen n` for `G`; for `H`,
the canonical encodings `encHQuery (false, m, c)` of a message `m` of length `msgLen n` and a
ciphertext `c` of length at most `ctLen n` (`WordPKE.isHQuery`); and ciphertexts of length at most
`ctLen n` for decapsulation. Any other request gets the empty reply and leaves the state
unchanged. The filter `d n pk gCache c` decides which decapsulation queries are answered. Every
query is answered for `FO-notbot` (`WordPKE.romCpaReductionWord`). For `FO^⊥`
(`WordPKE.romBotCpaReductionWord`) the filter is `Scheme.simBotCheck`, which answers a query only
when a cached `G` query re-encrypts to it under `encDet n pk`.

**The reduction.** `WordPKE.romFilterCpaReductionWord d A` mirrors
`Scheme.romFilterCpaReduction`. Its first stage draws `m₀, m₁` uniformly of length `msgLen n` and
saves the public key with `m₁`. Its second stage draws the challenge key `k*` of length `keyLen n`,
runs `A` against the simulator from empty caches (`WordPKE.simFilterWordHit`) and reports whether
`m₁` was queried to `G`.

**The certificate.** `WordPKE.IsEfficient.isPPT_romFilterCpaReductionWord` derives
`Encryption.AdversaryOf.IsPPT` of the reduction from `IsOraclePPT encBool A`, the efficiency of
the PKE family (`WordPKE.IsEfficient`), a polynomial-time key length and a polynomial-time filter;
the `FO^⊥` filter is polynomial-time whenever encryption is.
The simulator is substituted into `A` with `IsOraclePPT.run_interpret_preprocess`. Each call is
strict PPT in the full state (`WordPKE.IsEfficient.isPPTOn_simFilterWordHandler`), keeps every
cached value at most `coinLen n + keyLen n` bits long, and adds at most a polynomial in the
request length and `n` to the encoded state.

The advantages of the two instances are the typed `cpaAdvantage` of `Scheme.romCpaReduction` and
`Scheme.romBotCpaReduction` on a typed view of `A` (`WordPKE.IsEfficient.exists_typedAdversary` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordBridge`), and the asymptotic IND-CCA
theorems `WordPKE.INDCPA.romINDCCA` and `WordPKE.INDCPA.romINDCCABot` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordSecurity` apply the IND-CPA assumption
to them.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.CCAOp`: the oracle operations of an adversary.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encSimState`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encSimCall`: the encodings of the simulator state and of
  one simulator call.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.hQueryDecoder`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.isHQuery`: decoding and the domain of `H`
  requests.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.simFilterWordHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.simFilterWordHit`: the native keyless simulator
  and its run on a challenge.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encFilterInput`: the encoded input of a decapsulation
  filter.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romFilterCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romBotCpaReductionWord`: the native IND-CPA
  reduction, and its `FO-notbot` and `FO^⊥` instances.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.computableInPolyTime_isHQuery`: the
  `H` domain test is polynomial-time.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPTOn_simFilterWordHandler`: one
  simulator call is uniform strict PPT.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPT_romFilterCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPT_romCpaReductionWord`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.IsEfficient.isPPT_romBotCpaReductionWord`: the
  reductions are uniform strict PPT whenever the adversary is uniform strict oracle PPT.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021); the simulator and reduction are those of
  `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security`, which documents their relation
  to the source.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM

/-- Oracle operations of a word-level ROM IND-CCA adversary against an FO key encapsulation
mechanism: the random oracles `G` and `H`, and decapsulation. -/
inductive CCAOp where
  /-- Query the coin-derivation oracle `G`. -/
  | G
  /-- Query the key-derivation oracle `H`. -/
  | H
  /-- Query the decapsulation oracle. -/
  | decaps
  deriving DecidableEq

instance : FinEnum CCAOp := FinEnum.ofList [.G, .H, .decaps] (by intro x; cases x <;> simp)

/-- The state of the native keyless simulator: the caches of `SimState` over words, each an
association list. -/
enc_structure encSimState : SimState (List Bool) (List Bool) (List Bool) (List Bool) where
  gCache : (encMemoCache encBits encBits), hCache : (encMemoCache encHQuery encBits),
  hqCache : (encMemoCache encBits encBits)

/-- The input `((1ⁿ, pk, cStar), (op, w), st)` of one call of the native simulator: the
parameter, the public key and the challenge ciphertext, then the request and the simulator
state. -/
abbrev encSimCall : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) ×
    SimState (List Bool) (List Bool) (List Bool) (List Bool) ↪ List Bool :=
  encHandlerCall (encPair encUnary (encPair encBits encBits)) (encFinEnum CCAOp) encSimState

/-- The input `(1ⁿ, pk, gCache, c)` of a decapsulation filter of the native simulator: the
parameter in unary, then the public key, the cached `G` queries and the ciphertext. -/
abbrev encFilterInput : ℕ × List Bool × List (List Bool × List Bool) × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair (encMemoCache encBits encBits) encBits))

/-- The total decoder of `H` requests. -/
def hQueryDecoder : Decoder encHQuery := Decoder.bool.pair (Decoder.bits.pair Decoder.bits)

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- Whether the `H` request `w` is in the domain at parameter `n`: it is the canonical encoding
of `(false, m, c)` with `m` of length `msgLen n` and `c` of length at most `ctLen n`. -/
def isHQuery (n : ℕ) (w : List Bool) : Bool :=
  match hQueryDecoder.decode w with
  | (_, m, c) =>
    encHQuery (false, m, c) == w && m.length == P.msgLen n && decide (c.length ≤ P.ctLen n)

private theorem prefix_eq_false_of_isHQuery {P : WordPKE} {n : ℕ} {w : List Bool}
    (h : P.isHQuery n w = true) : (hQueryDecoder.decode w).1 = false := by
  simp only [isHQuery, Bool.and_eq_true, beq_iff_eq] at h
  have hd := congrArg hQueryDecoder.decode h.1.1
  rw [hQueryDecoder.decode_enc] at hd
  exact congrArg Prod.fst hd.symm

/-- The native keyless simulator with decapsulation filter `d` at parameter `n`, for public key
`pk` and challenge ciphertext `cStar`. A request in the domain is answered by the typed simulator
`Scheme.simFilterHandler` of the bundle `scheme P keyLen n`, on the same state; a decapsulation
answer is encoded with `encOption encBits`. A request outside the domain gets the empty reply and
leaves the state unchanged: a `G` request that is not a message of length `msgLen n`, an `H`
request that fails `isHQuery`, and a decapsulation request longer than `ctLen n`. -/
noncomputable def simFilterWordHandler
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (n : ℕ) (pk cStar : List Bool) (request : CCAOp × List Bool) :
    StateT (SimState (List Bool) (List Bool) (List Bool) (List Bool)) ProbComp (List Bool) :=
  fun st => match request with
  | (.G, m) =>
    if m.length = P.msgLen n then (P.scheme keyLen n).simFilterHandler (d n pk) pk cStar (.G m) st
    else pure ([], st)
  | (.H, w) =>
    if P.isHQuery n w then
      (P.scheme keyLen n).simFilterHandler (d n pk) pk cStar (.H (hQueryDecoder.decode w)) st
    else pure ([], st)
  | (.decaps, c) =>
    if c.length ≤ P.ctLen n then
      (fun (k, st') => (encOption encBits k, st')) <$>
        (P.scheme keyLen n).simFilterHandler (d n pk) pk cStar (.decaps c) st
    else pure ([], st)

/-- The native keyless simulator run inside the reduction: draw nothing, run the word adversary
`A` at parameter `n` on the challenge `(pk, kStar, cStar)` against `simFilterWordHandler d` from
empty caches, and report whether the target `m` was queried to `G`. -/
noncomputable def simFilterWordHit
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (A : ℕ → List Bool → WordOracleComp CCAOp Bool) (n : ℕ) (pk m cStar kStar : List Bool) :
    ProbComp Bool := do
  let (_, st) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (P.simFilterWordHandler keyLen d n pk cStar))
    (A n (Encryption.encKEMChallenge (pk, kStar, cStar)))).run {}
  return (st.gCache.lookup m).isSome

/-- **The native IND-CPA reduction** of the FO proofs with decapsulation filter `d`, for a word
adversary `A`, as a chosen-message adversary of `Encryption.gameOn`. The first stage draws both
challenge messages of length `msgLen n` and saves the public key with `m₁`. The second stage
draws the challenge key `kStar` of length `keyLen n` and runs `simFilterWordHit`, which reports
whether `m₁` was queried to `G`. It is the word-level counterpart of
`Scheme.romFilterCpaReduction`. -/
noncomputable def romFilterCpaReductionWord
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (A : ℕ → List Bool → WordOracleComp CCAOp Bool) : Encryption.AdversaryOf (List Bool) where
  choose n pk := do
    let m₀ ← BitString.sampleList (P.msgLen n)
    let m₁ ← BitString.sampleList (P.msgLen n)
    return ((m₀, m₁), encPair encBits encBits (pk, m₁))
  guess n state cStar := do
    let kStar ← BitString.sampleList (keyLen n)
    let (pk, m₁) := (Decoder.bits.pair Decoder.bits).decode state
    P.simFilterWordHit keyLen d A n pk m₁ cStar kStar

/-- **The native IND-CPA reduction for `FO-notbot`**: `romFilterCpaReductionWord` with every
decapsulation query answered, the word-level counterpart of `Scheme.romCpaReduction`. -/
noncomputable def romCpaReductionWord (A : ℕ → List Bool → WordOracleComp CCAOp Bool) :
    Encryption.AdversaryOf (List Bool) :=
  P.romFilterCpaReductionWord keyLen (fun _ _ _ _ => true) A

/-- **The native IND-CPA reduction for `FO^⊥`**: `romFilterCpaReductionWord` with the `FO^⊥`
filter `simBotCheck`, which answers a decapsulation query only when some cached `G` query
`(m, r)` re-encrypts to it under `encDet n pk`. It is the word-level counterpart of
`Scheme.romBotCpaReduction`. -/
noncomputable def romBotCpaReductionWord (A : ℕ → List Bool → WordOracleComp CCAOp Bool) :
    Encryption.AdversaryOf (List Bool) :=
  P.romFilterCpaReductionWord keyLen (fun n => Scheme.simBotCheck (P.toExplicitCoin n)) A

/-- The domain test of `H` requests is polynomial-time on `(1ⁿ, w)`. -/
theorem IsEfficient.computableInPolyTime_isHQuery {P : WordPKE} (hP : P.IsEfficient) :
    ComputableInPolyTime (fun (n, w) => P.isHQuery n w) (encPair encUnary encBits) encBool := by
  change ComputableInPolyTime (fun x : ℕ × List Bool =>
    encHQuery (false, (hQueryDecoder.decode x.2).2) == x.2 &&
      (hQueryDecoder.decode x.2).2.1.length == P.msgLen x.1 &&
      decide ((hQueryDecoder.decode x.2).2.2.length ≤ P.ctLen x.1))
    (encPair encUnary encBits) encBool
  have ⟨hmsgLen, _, hctLen, _, _, _⟩ := hP
  have := hQueryDecoder.computableInPolyTime
  have hcanon : ComputableInPolyTime
      (fun x : ℕ × List Bool => encHQuery (false, (hQueryDecoder.decode x.2).2) == x.2)
      (encPair encUnary encBits) encBool :=
    ComputableInPolyTime.beq
      ((ComputableInPolyTime.prod (.const false) (by polytime)).encoding_comp) (by polytime)
  exact (hcanon.bool_and' (by polytime)).bool_and' (by polytime)

/-! ### Certificates -/

section Certificates

/-- A lazily sampled cache inside the simulator state is uniform strict PPT: one `memoize` call
on the cache selected by `get`, drawing a word of length `len`, written back by `set`. -/
private theorem isPPTOn_zoomMemoize {Key : Type} [DecidableEq Key]
    {keyEncoding : Key ↪ List Bool}
    (get : SimState (List Bool) (List Bool) (List Bool) (List Bool) → List (Key × List Bool))
    (set : SimState (List Bool) (List Bool) (List Bool) (List Bool) → List (Key × List Bool) →
      SimState (List Bool) (List Bool) (List Bool) (List Bool))
    (hget : ComputableInPolyTime get encSimState (encMemoCache keyEncoding encBits))
    (hset : ComputableInPolyTime (fun p : SimState (List Bool) (List Bool) (List Bool) (List Bool) ×
        List (Key × List Bool) => set p.1 p.2)
      (encPair encSimState (encMemoCache keyEncoding encBits)) encSimState)
    {α : Type} {input : α ↪ List Bool} {len : α → ℕ} {key : α → Key}
    {st : α → SimState (List Bool) (List Bool) (List Bool) (List Bool)}
    (hlen : ComputableInPolyTime len input encUnary)
    (hkey : ComputableInPolyTime key input keyEncoding)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState) (fun a =>
      RandomOracle.zoomStateT get set (memoize (fun _ => BitString.sampleList (len a)) (key a))
        (st a)) := by
  refine ((IsPPTOn.memoize (compute := fun a _ => BitString.sampleList (len a))
    (query := key) (cache := fun a => get (st a)) hlen.sampleList hkey (hget.comp hst)).map_with
      (f := fun a p => (p.1, set (st a) p.2)) (by polytime)).congr fun a => ?_
  simp [RandomOracle.zoomStateT, bind_pure_comp]

/-- The simulator state `SimState` over words. -/
local notation "WState" => SimState (List Bool) (List Bool) (List Bool) (List Bool)

@[local fun_prop]
private theorem isPPTOn_simHashG {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {m : α → List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hm : ComputableInPolyTime m input encBits)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (len a)) (m a)
        (st a)) := by
  unfold simHashG
  exact isPPTOn_zoomMemoize (fun st => st.gCache) (fun st c => { st with gCache := c })
    (by fun_prop) (by fun_prop) hlen hm hst

@[local fun_prop]
private theorem isPPTOn_simHashHq {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {c : α → List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hc : ComputableInPolyTime c input encBits)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (len a)) (c a)
        (st a)) := by
  unfold simHashHq
  exact isPPTOn_zoomMemoize SimState.hqCache (fun st c' => { st with hqCache := c' })
    (by fun_prop) (by fun_prop) hlen hc hst

@[local fun_prop]
private theorem isPPTOn_simHashHRaw {α : Type} {input : α ↪ List Bool} {len : α → ℕ}
    {x : α → Bool × List Bool × List Bool} {st : α → WState}
    (hlen : ComputableInPolyTime len input encUnary) (hx : ComputableInPolyTime x input encHQuery)
    (hst : ComputableInPolyTime st input encSimState) :
    IsPPTOn input (encPair encBits encSimState)
      (fun a => simHashHRaw (R := List Bool) (BitString.sampleList (len a)) (x a) (st a)) := by
  unfold simHashHRaw
  exact isPPTOn_zoomMemoize (fun st => st.hCache) (fun st c => { st with hCache := c })
    (by fun_prop) (by fun_prop) hlen hx hst

/-- The simulator call on `x = ((n, pk, cStar), (op, w), st)` with every branch made explicit, for
the runtime certificate. -/
private noncomputable def simCallExplicit (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) :
    ProbComp (List Bool × WState) :=
  if x.2.1.1 = .G then
    if x.2.1.2.length = P.msgLen x.1.1 then
      simHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen x.1.1))
        x.2.1.2 x.2.2
    else pure ([], x.2.2)
  else if x.2.1.1 = .H then
    if P.isHQuery x.1.1 x.2.1.2 then do
      let (r, st₁) ← simHashG (CT := List Bool) (K := List Bool)
        (BitString.sampleList (P.coinLen x.1.1)) (hQueryDecoder.decode x.2.1.2).2.1 x.2.2
      if P.encDet x.1.1 x.1.2.1 (hQueryDecoder.decode x.2.1.2).2.1 r =
          (hQueryDecoder.decode x.2.1.2).2.2 then
        simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen x.1.1))
          (hQueryDecoder.decode x.2.1.2).2.2 st₁
      else
        simHashHRaw (R := List Bool) (BitString.sampleList (keyLen x.1.1))
          (false, (hQueryDecoder.decode x.2.1.2).2.1, (hQueryDecoder.decode x.2.1.2).2.2) st₁
    else pure ([], x.2.2)
  else
    if x.2.1.2.length ≤ P.ctLen x.1.1 then
      if x.2.1.2 = x.1.2.2 then pure (encOption encBits none, x.2.2)
      else if d x.1.1 x.1.2.1 x.2.2.gCache x.2.1.2 then
        (fun p => (encOption encBits (some p.1), p.2)) <$>
          simHashHq (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen x.1.1))
            x.2.1.2 x.2.2
      else pure (encOption encBits none, x.2.2)
    else pure ([], x.2.2)

private theorem simFilterWordHandler_eq_explicit (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool)
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState) :
    P.simFilterWordHandler keyLen d x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2 =
      simCallExplicit P keyLen d x := by
  obtain ⟨⟨n, pk, cStar⟩, ⟨op, w⟩, st⟩ := x
  cases op
  · rfl
  · simp only [simFilterWordHandler, simCallExplicit, reduceCtorEq, ↓reduceIte]
    by_cases hq : P.isHQuery n w = true
    · simp only [hq, ↓reduceIte, Scheme.simFilterHandler, Scheme.simFilterDispatch,
        ROQuery.dispatch]
      have hp := prefix_eq_false_of_isHQuery hq
      generalize hQueryDecoder.decode w = y at hp ⊢
      obtain ⟨b, m, c⟩ := y
      change b = false at hp
      subst b
      simp only [Scheme.simHashH, StateT.bind_apply, scheme, toExplicitCoin]
      congr 1 with p
      by_cases h : P.encDet n pk m p.1 = c <;> simp only [h, ↓reduceIte]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
  · simp only [simFilterWordHandler, simCallExplicit, reduceCtorEq, ↓reduceIte]
    by_cases hl : w.length ≤ P.ctLen n
    · simp only [hl, ↓reduceIte, Scheme.simFilterHandler, Scheme.simFilterDispatch,
        ROQuery.dispatch]
      by_cases hc : w = cStar
      · simp only [hc, ↓reduceIte]
        rfl
      · simp only [hc, ↓reduceIte, filterDecaps]
        cases d n pk st.gCache w
        · rfl
        · simp only [Bool.cond_true, ↓reduceIte, StateT.bind_apply, StateT.pure_apply,
            bind_pure_comp, Functor.map_map]
          rfl
    · simp only [hl, ↓reduceIte]

/-- The native simulator is uniform strict PPT on one call `((1ⁿ, pk, cStar), (op, w), st)`,
charging the complete state, whenever the PKE family and the decapsulation filter are
efficient. -/
theorem IsEfficient.isPPTOn_simFilterWordHandler {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool}
    (hd : ComputableInPolyTime (fun (n, pk, cache, c) => d n pk cache c) encFilterInput encBool) :
    IsPPTOn encSimCall (encPair encBits encSimState)
      (fun ((n, pk, cStar), request, st) =>
        P.simFilterWordHandler keyLen d n pk cStar request st) := by
  change IsPPTOn encSimCall (encPair encBits encSimState)
    (fun x => P.simFilterWordHandler keyLen d x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2)
  have ⟨hmsgLen, hcoinLen, hctLen, _, hencDet, _⟩ := hP
  have hisH := hP.computableInPolyTime_isHQuery
  have := hQueryDecoder.computableInPolyTime
  have hall : IsPPTOn encSimCall (encPair encBits encSimState) (simCallExplicit P keyLen d) := by
    ppt [simCallExplicit]
  exact hall.congr fun x => by rw [simFilterWordHandler_eq_explicit]

/-! ### Resource bounds of one simulator call -/

/-- Every value cached by the simulator has length at most `V`. -/
private def CachesBounded (V : ℕ) (st : WState) : Prop :=
  (∀ e ∈ st.gCache, e.2.length ≤ V) ∧ (∀ e ∈ st.hCache, e.2.length ≤ V) ∧
    ∀ e ∈ st.hqCache, e.2.length ≤ V

/-- One cached draw of a word of length `len ≤ V`: the reply has length at most `V`, and the new
cache keeps the bound and grows by at most one entry. -/
private theorem zoomMemoize_support {Key : Type} [DecidableEq Key] (keyEncoding : Key ↪ List Bool)
    (get : WState → List (Key × List Bool)) (set : WState → List (Key × List Bool) → WState)
    {len V : ℕ} (hlen : len ≤ V) (key : Key) (st : WState)
    (hcache : ∀ e ∈ get st, e.2.length ≤ V) (result : List Bool × WState)
    (hresult : result ∈ (ProbComp.eval (RandomOracle.zoomStateT get set
      (memoize (fun _ => BitString.sampleList len) key) st)).support) :
    result.1.length ≤ V ∧ ∃ c', result.2 = set st c' ∧ (∀ e ∈ c', e.2.length ≤ V) ∧
      (encMemoCache keyEncoding encBits c').length ≤
        (encMemoCache keyEncoding encBits (get st)).length + 4 * (keyEncoding key).length +
          2 * V + 3 := by
  rw [RandomOracle.eval_zoomStateT_memoize] at hresult
  obtain ⟨⟨v, c'⟩, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
  obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le keyEncoding encBits
    (fun _ => ProbComp.eval (BitString.sampleList len)) key (get st) V
    (by simpa only [encBits_apply] using hcache) (fun value hvalue => by
      rw [BitString.eval_sampleList] at hvalue
      simpa only [encBits_apply, BitString.length_of_mem_support_uniformList hvalue] using hlen)
    (v, c') hmem
  exact ⟨by simpa only [encBits_apply] using hreply, c', rfl,
    by simpa only [encBits_apply] using hcache', hgrowth⟩

private theorem length_encSimState (st : WState) :
    (encSimState st).length = 2 * (encMemoCache encBits encBits st.gCache).length +
      2 * (encMemoCache encHQuery encBits st.hCache).length +
        (encMemoCache encBits encBits st.hqCache).length + 2 := by
  simp only [encSimState_apply, encSimStateFields, length_encPair]
  ring

private theorem length_encHQuery (b : Bool) (m c : List Bool) :
    (encHQuery (b, m, c)).length = 2 * m.length + c.length + 4 := by
  simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
  ring

/-- A request in the `H` domain bounds the lengths of its message and ciphertext. -/
private theorem length_le_of_isHQuery {P : WordPKE} {n : ℕ} {w : List Bool}
    (h : P.isHQuery n w = true) :
    2 * (hQueryDecoder.decode w).2.1.length + (hQueryDecoder.decode w).2.2.length + 4 =
      w.length := by
  unfold isHQuery at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hlen := congrArg List.length h.1.1
  rw [length_encHQuery] at hlen
  exact hlen

/-- One call of the simulator keeps every cached value of length at most `V`, replies with at most
`V + 1` bits, and adds at most `16 |w| + 8 V + 12` bits of encoded state for a request word `w`,
when coins and keys have length at most `V`. -/
private theorem simCallExplicit_support (P : WordPKE) (keyLen : ℕ → ℕ)
    (d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool) {V : ℕ}
    (x : (ℕ × List Bool × List Bool) × (CCAOp × List Bool) × WState)
    (hcoin : P.coinLen x.1.1 ≤ V) (hkey : keyLen x.1.1 ≤ V) (hinv : CachesBounded V x.2.2)
    (result : List Bool × WState)
    (hresult : result ∈ (ProbComp.eval (simCallExplicit P keyLen d x)).support) :
    CachesBounded V result.2 ∧ result.1.length ≤ V + 1 ∧
      (encSimState result.2).length ≤
        (encSimState x.2.2).length + 16 * x.2.1.2.length + 8 * V + 12 := by
  obtain ⟨⟨n, pk, cStar⟩, ⟨op, w⟩, st⟩ := x
  obtain ⟨hg, hh, hq⟩ := hinv
  -- the three cached draws
  have stepG (m : List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀) (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashG (CT := List Bool) (K := List Bool)
        (BitString.sampleList (P.coinLen n)) m st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤ (encSimState st₀).length + 8 * m.length + 4 * V + 6 := by
    unfold simHashG at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encBits (fun st => st.gCache)
      (fun st c => { st with gCache := c }) hcoin m st₀ h₀.1 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨hc', h₀.2⟩
    · rw [hnext, length_encSimState, length_encSimState]
      simp only [encBits_apply] at hlen
      lia
  have stepHq (c : List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀) (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashHq (M := List Bool) (R := List Bool)
        (BitString.sampleList (keyLen n)) c st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤ (encSimState st₀).length + 4 * c.length + 2 * V + 3 := by
    unfold simHashHq at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encBits SimState.hqCache
      (fun st c' => { st with hqCache := c' }) hkey c st₀ h₀.2.2 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨h₀.1, h₀.2.1, hc'⟩
    · rw [hnext, length_encSimState, length_encSimState]
      simp only [encBits_apply] at hlen
      lia
  have stepHRaw (y : Bool × List Bool × List Bool) (st₀ : WState) (h₀ : CachesBounded V st₀)
      (r : List Bool × WState)
      (hr : r ∈ (ProbComp.eval (simHashHRaw (R := List Bool)
        (BitString.sampleList (keyLen n)) y st₀)).support) :
      CachesBounded V r.2 ∧ r.1.length ≤ V ∧
        (encSimState r.2).length ≤
          (encSimState st₀).length + 8 * (encHQuery y).length + 4 * V + 6 := by
    unfold simHashHRaw at hr
    obtain ⟨hreply, c', hnext, hc', hlen⟩ := zoomMemoize_support encHQuery (fun st => st.hCache)
      (fun st c => { st with hCache := c }) hkey y st₀ h₀.2.1 r hr
    refine ⟨?_, hreply, ?_⟩
    · rw [hnext]; exact ⟨h₀.1, hc', h₀.2.2⟩
    · rw [hnext, length_encSimState, length_encSimState]
      lia
  have hinv : CachesBounded V st := ⟨hg, hh, hq⟩
  have hpure (v : List Bool) (hv : v.length ≤ V + 1)
      (hr : result ∈ (ProbComp.eval (pure (v, st) : ProbComp (List Bool × WState))).support) :
      CachesBounded V result.2 ∧ result.1.length ≤ V + 1 ∧
        (encSimState result.2).length ≤ (encSimState st).length + 16 * w.length + 8 * V + 12 := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hr
    subst hr
    exact ⟨hinv, hv, by lia⟩
  cases op
  · simp only [simCallExplicit, ↓reduceIte] at hresult ⊢
    split_ifs at hresult
    · obtain ⟨h₁, h₂, h₃⟩ := stepG w st hinv result hresult
      exact ⟨h₁, by lia, by lia⟩
    · exact hpure [] (by simp) hresult
  · simp only [simCallExplicit, reduceCtorEq, ↓reduceIte] at hresult ⊢
    split_ifs at hresult with hvalid
    · have hw := length_le_of_isHQuery hvalid
      rw [ProbComp.eval_bind] at hresult
      obtain ⟨r, hr, hresult⟩ := (PMF.mem_support_bind_iff _ _ _).mp hresult
      obtain ⟨h₁, -, h₃⟩ := stepG _ st hinv r hr
      split_ifs at hresult
      · obtain ⟨h₄, h₅, h₆⟩ := stepHq _ r.2 h₁ result hresult
        exact ⟨h₄, by lia, by lia⟩
      · obtain ⟨h₄, h₅, h₆⟩ := stepHRaw _ r.2 h₁ result hresult
        rw [length_encHQuery] at h₆
        exact ⟨h₄, by lia, by lia⟩
    · exact hpure [] (by simp) hresult
  · simp only [simCallExplicit, reduceCtorEq, ↓reduceIte] at hresult ⊢
    split_ifs at hresult
    · exact hpure _ (by simp) hresult
    · rw [ProbComp.eval_map] at hresult
      obtain ⟨r, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      obtain ⟨h₁, h₂, h₃⟩ := stepHq w st hinv r hr
      refine ⟨h₁, ?_, by lia⟩
      simp only [encOption_some, List.length_cons, encBits_apply]
      lia
    · exact hpure _ (by simp) hresult
    · exact hpure [] (by simp) hresult

private theorem lookup_isSome_eq_any (m : List Bool) (cache : List (List Bool × List Bool)) :
    (cache.lookup m).isSome = cache.any fun e => e.1 == m := by
  induction cache with
  | nil => rfl
  | cons e cache ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : m = k
    · subst h; simp [List.lookup]
    · simp [List.lookup, beq_eq_false_iff_ne.mpr h, ih, Ne.symm h]

/-- The guessing stage of the reduction after its key draw, on `((n, state, cStar), kStar)`. -/
private abbrev encGuessKey : (ℕ × List Bool × List Bool) × List Bool ↪ List Bool :=
  encPair Encryption.encGuessInput encBits

/-- **The reduction is uniform strict PPT.** For an efficient PKE family, a polynomial-time key
length and an efficient decapsulation filter, the word-level IND-CPA reduction of every
uniform strict oracle PPT ROM IND-CCA adversary is a uniform strict PPT chosen-message adversary.
The certificate covers the lazy `G`/`H` simulation and the simulated decapsulation oracle. -/
theorem IsEfficient.isPPT_romFilterCpaReductionWord {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {d : ℕ → List Bool → List (List Bool × List Bool) → List Bool → Bool}
    (hd : ComputableInPolyTime (fun (n, pk, cache, c) => d n pk cache c) encFilterInput encBool)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    (P.romFilterCpaReductionWord keyLen d A).IsPPT encBits where
  choose := by
    have ⟨hmsgLen, _, _, _, _, _⟩ := hP
    ppt [romFilterCpaReductionWord]
  guess := by
    change IsPPTOn Encryption.encGuessInput encBool (fun x =>
      (P.romFilterCpaReductionWord keyLen d A).guess x.1 x.2.1 x.2.2)
    let D := Decoder.bits.pair Decoder.bits
    have hD := D.computableInPolyTime
    have hcoinLen := hP.coinLen
    have hhandler : IsPPTOn (encHandlerCall encGuessKey (encFinEnum CCAOp) encSimState)
        (encPair encBits encSimState)
        (fun z : ((ℕ × List Bool × List Bool) × List Bool) × (CCAOp × List Bool) × WState =>
          P.simFilterWordHandler keyLen d z.1.1.1 (D.decode z.1.1.2.1).1
            z.1.1.2.2 z.2.1 z.2.2) := by
      refine (hP.isPPTOn_simFilterWordHandler hkeyLen hd).preprocess
        (prepare := fun z : ((ℕ × List Bool × List Bool) × List Bool) × (CCAOp × List Bool) ×
            WState =>
          ((z.1.1.1, (D.decode z.1.1.2.1).1, z.1.1.2.2), z.2.1, z.2.2)) ?_
      polytime
    have hrun := hA.run_interpret_preprocess (operationEncoding := encFinEnum CCAOp)
      (stateEncoding := encSimState)
      (handler := fun (c : (ℕ × List Bool × List Bool) × List Bool) request st =>
        P.simFilterWordHandler keyLen d c.1.1 (D.decode c.1.2.1).1 c.1.2.2 request st)
      (prepare := fun c : (ℕ × List Bool × List Bool) × List Bool =>
        (c.1.1, Encryption.encKEMChallenge ((D.decode c.1.2.1).1, c.2, c.1.2.2)))
      (initial := fun _ => {})
      (resources := fun (c : (ℕ × List Bool × List Bool) × List Bool) w =>
        16 * w.length + 8 * (P.coinLen c.1.1 + keyLen c.1.1) + 13)
      (by polytime)
      hhandler (.const _)
      (fun (c : (ℕ × List Bool × List Bool) × List Bool) st =>
        CachesBounded (P.coinLen c.1.1 + keyLen c.1.1) st)
      (fun _ => ⟨by simp, by simp, by simp⟩)
      (by polytime)
      (fun c request st hst result hresult => by
        have hx := simFilterWordHandler_eq_explicit P keyLen d
          ((c.1.1, (D.decode c.1.2.1).1, c.1.2.2), request, st)
        change P.simFilterWordHandler keyLen d c.1.1 (D.decode c.1.2.1).1 c.1.2.2 request st =
          _ at hx
        rw [hx] at hresult
        obtain ⟨h₁, h₂, h₃⟩ := simCallExplicit_support P keyLen d _ (Nat.le_add_right _ _)
          (Nat.le_add_left _ _) hst result hresult
        exact ⟨h₁, by lia, by lia⟩)
    have hlookup : ComputableInPolyTime
        (fun q : ((ℕ × List Bool × List Bool) × List Bool) × (Bool × WState) =>
          (q.2.2.gCache.lookup (D.decode q.1.1.2.1).2).isSome)
        (encPair encGuessKey (encPair encBool encSimState)) encBool := by
      simp only [lookup_isSome_eq_any]
      exact ComputableInPolyTime.anyWithInput (by polytime) (by polytime)
    have hall := IsPPTOn.bind_with
      (first := fun x : ℕ × List Bool × List Bool => BitString.sampleList (keyLen x.1))
      (second := fun x kStar =>
        (fun q : Bool × WState => (q.2.gCache.lookup (D.decode x.2.1).2).isSome) <$>
          (OracleComp.interpret
            (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) fun request st =>
              P.simFilterWordHandler keyLen d x.1 (D.decode x.2.1).1 x.2.2 request st)
            (A x.1 (Encryption.encKEMChallenge ((D.decode x.2.1).1, kStar, x.2.2)))).run {})
      (by ppt) (hrun.map_with (f := fun c q => (q.2.gCache.lookup (D.decode c.1.2.1).2).isSome)
        hlookup)
    refine hall.congr fun x => ?_
    simp only [romFilterCpaReductionWord, simFilterWordHit, bind_pure_comp]
    rfl

/-- The input `(n, pk, gCache, c)` of a decapsulation filter. -/
local notation "FilterInput" => ℕ × List Bool × List (List Bool × List Bool) × List Bool

/-- A cached `G` query `(m, r)`. -/
local notation "Entry" => List Bool × List Bool

/-- The `FO^⊥` filter `simBotCheck` of the explicit-coin scheme at parameter `n` is polynomial-time
on `(1ⁿ, pk, gCache, c)`. -/
private theorem IsEfficient.computableInPolyTime_simBotCheck {P : WordPKE}
    (hP : P.IsEfficient) :
    ComputableInPolyTime
      (fun (n, pk, cache, c) => Scheme.simBotCheck (P.toExplicitCoin n) pk cache c)
      encFilterInput encBool := by
  have hencDet := hP.encDet
  have hfind : ComputableInPolyTime (fun p : FilterInput × Entry => p.1.2.2.1.find? fun e =>
      decide (p.2.1 = e.1)) (encPair encFilterInput (encPair encBits encBits))
      (encOption (encPair encBits encBits)) :=
    ComputableInPolyTime.findWithInput (by polytime) (by polytime)
  have htest := ComputableInPolyTime.optionElimWithInput (body := fun (p : FilterInput × Entry)
      (e : Entry) => decide (P.encDet p.1.1 p.1.2.1 p.2.1 e.2 = p.1.2.2.2)) hfind
    (.const false) (by polytime)
  have heq : (fun x : FilterInput => Scheme.simBotCheck (P.toExplicitCoin x.1) x.2.1 x.2.2.1
      x.2.2.2) = fun x => x.2.2.1.any fun p => (x.2.2.1.find? fun e => decide (p.1 = e.1)).elim
        false fun e => decide (P.encDet x.1 x.2.1 p.1 e.2 = x.2.2.2) := by
    funext ⟨n, pk, cache, c⟩
    simp only [Scheme.simBotCheck, List.lookup_eq_map_find?]
    congr 1 with p : 1
    cases List.find? (fun e => decide (p.1 = e.1)) cache <;> rfl
  change ComputableInPolyTime (fun x : FilterInput => Scheme.simBotCheck (P.toExplicitCoin x.1)
    x.2.1 x.2.2.1 x.2.2.2) encFilterInput encBool
  rw [heq]
  exact ComputableInPolyTime.anyWithInput (by polytime) htest

/-- **The `FO^⊥` reduction is uniform strict PPT.** For an efficient PKE family and a
polynomial-time key length, the word-level IND-CPA reduction `romBotCpaReductionWord A` of every
uniform strict oracle PPT ROM IND-CCA adversary `A` is a uniform strict PPT chosen-message
adversary. -/
theorem IsEfficient.isPPT_romBotCpaReductionWord {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    (P.romBotCpaReductionWord keyLen A).IsPPT encBits :=
  hP.isPPT_romFilterCpaReductionWord hkeyLen hP.computableInPolyTime_simBotCheck hA

/-- **The `FO-notbot` reduction is uniform strict PPT.** For an efficient PKE family and a
polynomial-time key length, the word-level IND-CPA reduction `romCpaReductionWord A` of every
uniform strict oracle PPT ROM IND-CCA adversary `A` is a uniform strict PPT chosen-message
adversary. -/
theorem IsEfficient.isPPT_romCpaReductionWord {P : WordPKE} (hP : P.IsEfficient)
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {A : ℕ → List Bool → WordOracleComp CCAOp Bool} (hA : IsOraclePPT encBool A) :
    (P.romCpaReductionWord keyLen A).IsPPT encBits :=
  hP.isPPT_romFilterCpaReductionWord hkeyLen (d := fun _ _ _ _ => true)
    (ComputableInPolyTime.const true) hA

end Certificates

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
