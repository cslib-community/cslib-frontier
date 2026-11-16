/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Primitives.CorrelationRobust
public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Correlation-robust hash functions

The finite notion `Cslib.Crypto.CorrelationRobust.advantage` measures how well one test tells
`(t, fun j => H j (t j + s))` from `(t, u)`, for uniform `s`, `t` and `u`, for one family `H` on
finite types. This module states the asymptotic assumption on a hash given on words,
`hash : List Bool → Bool`, in the form of Definition 1 of Ishai, Kilian, Nissim and Petrank
[IshaiKilianNissimPetrank2003] (§5, p. 157): an efficiently computable `h : {0,1}* → {0,1}` is
correlation robust if for uniform `k`-bit strings `s, t₁, …, tₘ` the bits
`h(t₁ ⊕ s), …, h(tₘ ⊕ s)` are pseudorandom given `t₁, …, tₘ`, for polynomially many `m`.

At level `k` with `m` queries, `CorrelationRobust.atLevel hash k m` hashes the word of the `k` bits
of each input with `hash`, the same function at every position. A distinguisher for the query
count `m : ℕ → ℕ` (`CorrelationRobust.Distinguisher m`) is a finite test at each level `k` on
`m k` inputs of `k` bits and `m k` output bits. It is PPT (`CorrelationRobust.Distinguisher.IsPPT`)
when one uniform strict PPT machine reads `CorrelationRobust.encInput m`: the unary level, the
framed list of the input words and the word of the output bits, and writes the test's bit.

`CorrelationRobust hash` asks that the hash be computable in polynomial time and that, for every
polynomially bounded query count `m`, every PPT distinguisher have negligible advantage. Its
level-`k` advantage is, by definition, the finite advantage
`CorrelationRobust.advantage (CorrelationRobust.atLevel hash k (m k)) (D k)`, so the finite
theorems about that advantage apply at every level without a bridge.

## Relation to the source

The two parts of the assumption are Definition 1's two conditions. `polyTime` reads "efficiently
computable" as one deterministic polynomial-time machine on all words. The security condition
`secure` differs from Definition 1 as follows; each difference admits fewer distinguishers, so for
a hash with `polyTime`, Definition 1 implies `secure`.

* **Distinguishers** are uniform strict PPT machines, where Definition 1 has circuits of size
  `p(k)`. A machine's clock is polynomial in the length of its input, which for a polynomially
  bounded `m` is polynomial in `k`.
* **Query counts.** The count is a fixed polynomially bounded function `m` of the level, with a
  negligible function for each such `m`, where Definition 1 has one negligible function for all
  `m ≤ q(k)` for each polynomial `q`.

The bound on `m` is needed. With `m k = 2 ^ k` queries, a distinguisher whose clock is polynomial
in its input length can try every `s` against all the outputs, so the condition without the bound
would fail for every hash computed in polynomial time.

The protocol of [IshaiKilianNissimPetrank2003] (Fig. 1, p. 152) hashes `(j, u)` with a random
oracle `H : [m] × {0,1}^k → {0,1}^ℓ`; §5 (p. 157, with footnote 10) replaces it by a correlation
robust `h` for bit transfers (`ℓ = 1`), hashing `u` alone. `CorrelationRobust.atLevel` is that
replacement: it ignores the position.

## Main definitions

* `Cslib.Crypto.CorrelationRobust.atLevel`: the hash of a word function at level `k`.
* `Cslib.Crypto.CorrelationRobust.Distinguisher`, `Cslib.Crypto.CorrelationRobust.Input`,
  `Cslib.Crypto.CorrelationRobust.encInput`, `Cslib.Crypto.CorrelationRobust.Distinguisher.IsPPT`:
  distinguishers, what they read, and their efficiency.
* `Cslib.Crypto.CorrelationRobust`: the asymptotic assumption.

This module has definitions only. The test module `CslibFrontierTests.Crypto.CorrelationRobust`
shows that a constant hash is not correlation robust.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003], §5 (Definition 1, p. 157).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace CorrelationRobust

/-- The hash of the word function `hash` at level `k`, for `m` queries: every position hashes the
word `List.ofFn t` of the `k` bits of its input with `hash`. -/
@[expose] def atLevel (hash : List Bool → Bool) (k m : ℕ) : Fin m → BitString k → Bool :=
  fun _ t => hash (List.ofFn t)

/-- A distinguisher for the query count `m`: at each level `k`, a test on `m k` inputs of `k` bits
and `m k` output bits. `Distinguisher.IsPPT` states its efficiency. -/
abbrev Distinguisher (m : ℕ → ℕ) : Type :=
  (k : ℕ) → Adversary (m k) (BitString k) Bool

/-- The word of `count` inputs of `k` bits: the framed list (`encList encBits`) of their bit
words. -/
@[expose] noncomputable def inputsWord (k count : ℕ) (t : Fin count → BitString k) : List Bool :=
  encList encBits (List.ofFn fun j => List.ofFn (t j))

/-- The word of the inputs determines them. -/
theorem inputsWord_injective (k count : ℕ) : Function.Injective (inputsWord k count) :=
  fun _ _ h => funext fun j =>
    List.ofFn_injective (congrFun (List.ofFn_injective ((encList encBits).injective h)) j)

/-- The input of a distinguisher for the query count `m`, as a record: the level, the `m level`
inputs and the `m level` output bits. -/
structure Input (m : ℕ → ℕ) where
  /-- The level, given to machines in unary. -/
  level : ℕ
  /-- The inputs `t₁, …, tₘ`. -/
  inputs : Fin (m level) → BitString level
  /-- The output bits. -/
  outputs : BitString (m level)

noncomputable section

/-- The encoding of a distinguisher's input: the unary level, the word of the inputs (`inputsWord`)
and the word of the output bits (`encBitString`), each framed except the last. -/
enc_structure encInput (m : ℕ → ℕ) : Input m where
  level : encUnary,
  inputs : (inputsWord level (m level)) using (inputsWord_injective level (m level)),
  outputs : (encBitString (m level)) using (encBitString (m level)).injective

end

variable {m : ℕ → ℕ}

/-- A distinguisher is PPT when one uniform strict PPT machine reads `encInput m` and writes the
test's bit. -/
@[expose] def Distinguisher.IsPPT (D : Distinguisher m) : Prop :=
  IsPPTOn (encInput m) encBool fun x => D x.level (x.inputs, x.outputs)

end CorrelationRobust

/-- **Correlation robustness** of a hash on words ([IshaiKilianNissimPetrank2003], Definition 1,
§5, p. 157): the hash is evaluated in polynomial time, and for every polynomially bounded query
count `m` and at every level `k`, no uniform strict PPT distinguisher tells the inputs `t` with the
bits `hash (t j + s)`, for a uniform `k`-bit `s`, from `t` with uniform bits, except with
negligible advantage. The distinguishers are uniform and the negligible function may depend on
`m`; Definition 1 implies the security condition (module documentation). -/
structure CorrelationRobust (hash : List Bool → Bool) : Prop where
  /-- One deterministic machine evaluates the hash. -/
  polyTime : ComputableInPolyTime hash encBits encBool
  /-- For every polynomially bounded query count `m`, the finite real and ideal games of
  `CorrelationRobust.atLevel hash k (m k)` at level `k` are indistinguishable for PPT
  distinguishers. -/
  secure : ∀ m : ℕ → ℕ, PolynomiallyBounded m →
    Game.Indistinguishable
      (fun (D : CorrelationRobust.Distinguisher m) k =>
        CorrelationRobust.realGame (CorrelationRobust.atLevel hash k (m k)) (D k))
      (fun D k => CorrelationRobust.idealGame (D k))
      CorrelationRobust.Distinguisher.IsPPT

end Cslib.Crypto
