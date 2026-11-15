/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Family
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# K-PKE with PRF seed expansion

Kyber v3.02 expands every centered-binomial noise polynomial of K-PKE from a 32-byte seed with a
pseudorandom function `PRF : B^32 × B → B^*` ([AvanziEtAl2021], p. 5), reading `64η` bytes with
`CBD_η` (Algorithm 2, p. 7). Key generation computes `s[i], e[i] := CBD_η₁(PRF(σ, N))` for the
counters `N = 0, …, 2k − 1`, where `σ` is half of `G(d)` (Algorithm 4, p. 8). Encryption with
coins `r ∈ B^32` computes `r[i] := CBD_η₁(PRF(r, N))`, `e₁[i] := CBD_η₂(PRF(r, N))` and
`e₂ := CBD_η₂(PRF(r, N))` for `N = 0, …, 2k` (Algorithm 5, p. 9).

`kpkePRF P F` is the word-level K-PKE family `kpke P` of
`CslibFrontier.Crypto.Computational.SIS.MLKEM.Family` with this expansion by a keyed function `F`
on words, in place of fair coins. At security parameter `κ`:

* the encryption coins are a `κ`-bit seed `r`, expanded to `encNoise (P κ) F r`: for each counter
  `N ≤ 2k`, the first `n · 2η` bits of `F r (nonceWord N)`, with `η = η₁` for `N < k` and
  `η = η₂` otherwise (`encWidth`). These are exactly the bits from which `encDetWord` decodes the
  `N`-th noise polynomial by `SamplePolyCBD_η`;
* key generation draws the matrix as `keyGenWord` does, and a uniform `κ`-bit seed `σ`, and decodes
  `s` and `e` from `keyNoise (P κ) F σ`, the first `n · 2η₁` bits of `F σ (nonceWord N)` for
  `N < 2k`;
* decryption is `decWord`.

The counter `N` is written in binary in `nonceLen = (2k).size` bits, so the `2k + 1` counters have
distinct words for every rank `k` (`nonceWord_injOn`). The PRF's outputs are meant to have
`prfLen = n · 2 · max(η₁, η₂)` bits, of which each counter reads a prefix.

The family is efficient whenever its parameters are computable in polynomial time and `F` is
evaluated in polynomial time (`kpkePRF_isEfficient`), and its ciphertexts fit the ciphertext space
(`kpkePRF_ciphertextFits`). This module makes no security claim.

## Model differences from Kyber v3.02 and FIPS 203

* The matrix is drawn coefficientwise, approximately uniformly, rather than expanded from `ρ` by
  `XOF`, and the seed `σ` is uniform rather than half of `G(d)`. This is how Kyber v3.02
  Theorem 1 (§4.3.1, p. 20) treats `XOF` and `G`, as random oracles.
* Seeds have `κ` bits rather than 32 bytes, and counters `(2k).size` bits rather than one byte,
  since an asymptotic family scales the rank `k`.
* `F` is any keyed function on words. Kyber's `PRF` has outputs of any length and FIPS 203 fixes
  it to SHAKE-256 (`prf` of `CslibFrontier.Crypto.Computational.SIS.MLKEM.SeedExpansion`), whose
  outputs of different lengths are prefixes of one another (`prf_two_eq_take_three`).
* Polynomials are in coefficient form rather than the NTT domain, and keys and ciphertexts are
  words of residue lists rather than `ByteEncode` outputs.

## Main definitions

* `Cslib.Crypto.MLKEM.nonceLen`, `Cslib.Crypto.MLKEM.nonceWord`, `Cslib.Crypto.MLKEM.prfLen`: the
  counter words and the PRF output length.
* `Cslib.Crypto.MLKEM.expandNoise`, `Cslib.Crypto.MLKEM.keyNoise`, `Cslib.Crypto.MLKEM.encWidth`,
  `Cslib.Crypto.MLKEM.encNoise`: seed expansion.
* `Cslib.Crypto.MLKEM.keyGenPRFWord`: key generation with seed expansion.
* `Cslib.Crypto.MLKEM.kpkePRF`: the word-level K-PKE family with seed expansion.

## Main results

* `Cslib.Crypto.MLKEM.nonceWord_injOn`: the counters of key generation and encryption have
  distinct words.
* `Cslib.Crypto.MLKEM.kpkePRF_isEfficient`: the family is efficient for a polynomial-time
  parameter family and a polynomial-time `F`.
* `Cslib.Crypto.MLKEM.kpkePRF_ciphertextFits`: ciphertexts fit their ciphertext space.

## References

* [R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation
  (version 3.02)*][AvanziEtAl2021], 4 August 2021, p. 5, Algorithms 2, 4 and 5 (pp. 7–9) and
  §4.3.1 (p. 20)
* [NIST, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*][NISTFIPS203]
-/

@[expose] public section

namespace Cslib.Crypto.MLKEM

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.FujisakiOkamoto

/-! ### Counters and seed expansion -/

/-- The number of bits of a PRF counter word: the length of the binary representation of `2k`, so
that the counters `0, …, 2k` of key generation and encryption have distinct words. -/
def nonceLen (P : Params) : ℕ := (2 * P.k).size

/-- The word of the PRF counter `N`: its `nonceLen P` low-order bits, least significant first. -/
def nonceWord (P : Params) (N : ℕ) : List Bool := BitString.lowBits (nonceLen P) N

/-- The output length of the PRF, `n · 2 · max(η₁, η₂)` bits: `SamplePolyCBD_η` reads the first
`n · 2η` of them at either width. -/
def prfLen (P : Params) : ℕ := P.n * (2 * max P.η₁ P.η₂)

/-- Seed expansion: for each counter `N < count`, the first `width N` bits of `F seed` at the word
of `N`, concatenated. -/
def expandNoise (P : Params) (F : List Bool → List Bool → List Bool) (seed : List Bool)
    (count : ℕ) (width : ℕ → ℕ) : List Bool :=
  (List.range count).flatMap fun N => (F seed (nonceWord P N)).take (width N)

/-- The noise bits of key generation from the seed `σ`: `n · 2η₁` bits from each of the counters
`0, …, 2k − 1`, those of `s` and then those of `e`. -/
def keyNoise (P : Params) (F : List Bool → List Bool → List Bool) (σ : List Bool) : List Bool :=
  expandNoise P F σ (2 * P.k) fun _ => P.n * (2 * P.η₁)

/-- The number of noise bits that encryption reads from counter `N`: `n · 2η₁` for the `k`
polynomials of `r`, and `n · 2η₂` for the `k` polynomials of `e₁` and for `e₂`. -/
def encWidth (P : Params) (N : ℕ) : ℕ :=
  if N < P.k then P.n * (2 * P.η₁) else P.n * (2 * P.η₂)

/-- The coins of encryption from the seed `r`: the noise bits of the counters `0, …, 2k`. -/
def encNoise (P : Params) (F : List Bool → List Bool → List Bool) (r : List Bool) : List Bool :=
  expandNoise P F r (2 * P.k + 1) (encWidth P)

@[simp] theorem length_nonceWord (P : Params) (N : ℕ) : (nonceWord P N).length = nonceLen P :=
  BitString.length_lowBits _ _

/-- **The counters have distinct words.** The words of the counters `0, …, 2k` are distinct. -/
theorem nonceWord_injOn (P : Params) : Set.InjOn (nonceWord P) (Set.Iic (2 * P.k)) := by
  intro N hN M hM h
  have hlt (x : ℕ) (hx : x ≤ 2 * P.k) : x < 2 ^ nonceLen P :=
    lt_of_le_of_lt hx (Nat.lt_size_self _)
  exact BitString.lowBits_injective_of_lt (hlt N hN) (hlt M hM) h

/-! ### Key generation and the family -/

/-- K-PKE key generation on words with PRF seed expansion: draw the matrix as `keyGenWord` does at
precision `κ` and a uniform `κ`-bit seed `σ`, and decode `s` and `e` from `keyNoise P F σ`. -/
noncomputable def keyGenPRFWord (P : Params) (F : List Bool → List Bool → List Bool) (κ : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let A ← sampleMatrixResidues P κ
  let σ ← BitString.sampleList κ
  return keyWords P A ((keyNoise P F σ).take (P.k * (P.n * (2 * P.η₁))))
    ((keyNoise P F σ).drop (P.k * (P.n * (2 * P.η₁))))

/-- **K-PKE with PRF seed expansion as a word-level public-key encryption family.** At security
parameter `κ`, the scheme uses the parameters `P κ` and the keyed function `F`: key generation is
`keyGenPRFWord`, encryption coins are `κ`-bit seeds expanded by `encNoise`, and messages,
ciphertexts and decryption are those of `kpke P`. -/
noncomputable def kpkePRF (P : ℕ → Params) (F : List Bool → List Bool → List Bool) : WordPKE where
  msgLen κ := (P κ).n
  coinLen κ := κ
  ctLen κ := ctLength (P κ)
  keyGen κ := keyGenPRFWord (P κ) F κ
  encDet κ pk m r := encDetWord (P κ) pk m (encNoise (P κ) F r)
  dec κ := decWord (P κ)

/-- **K-PKE ciphertexts with seed expansion fit their ciphertext space.** -/
theorem kpkePRF_ciphertextFits (P : ℕ → Params) (F : List Bool → List Bool → List Bool) :
    (kpkePRF P F).CiphertextFits :=
  fun κ pk _ _ m r _ _ => length_encDetWord_le (P κ) pk m (encNoise (P κ) F r)

/-! ### Polynomial-time certificates -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The word of a computed counter, with computed parameters. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.nonceWord {P : α → Params} {N : α → ℕ}
    (hP : ComputableInPolyTime P input encParams) (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun a => nonceWord (P a) (N a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.nonceWord Cslib.Crypto.MLKEM.nonceLen
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have hsize : ComputableInPolyTime (fun a => (2 * (P a).k).size) input encUnary :=
    ComputableInPolyTime.binary_size.comp
      (ComputableInPolyTime.unary_to_binary.comp
        (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hk)))
  exact ComputableInPolyTime.bitsLow hsize (ComputableInPolyTime.unary_to_binary.comp hN)

/-- Seed expansion with computed parameters, seed, count and widths, for a keyed function
evaluated in polynomial time. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.expandNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {seed : α → List Bool} {count : α → ℕ}
    {width : α → ℕ → ℕ} (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hseed : ComputableInPolyTime seed input encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime (fun p : α × ℕ => width p.1 p.2) (encPair input encUnary)
      encUnary) :
    ComputableInPolyTime (fun a => expandNoise (P a) F (seed a) (count a) (width a)) input
      encBits := by
  unfold Cslib.Crypto.MLKEM.expandNoise
  have hfst := ComputableInPolyTime.fst input encUnary
  have hsnd := ComputableInPolyTime.snd input encUnary
  have hvalue := hF.comp ((hseed.comp hfst).prod
    (ComputableInPolyTime.nonceWord (hP.comp hfst) hsnd))
  exact ComputableInPolyTime.flatMapToBitsWithInput (enc := encUnary)
    (ComputableInPolyTime.range.comp hcount)
    (ComputableInPolyTime.bitsTakeWithInput hvalue hwidth)

/-- The noise widths of encryption, with computed parameters and counter. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encWidth {P : α → Params} {N : α → ℕ}
    (hP : ComputableInPolyTime P input encParams) (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun a => encWidth (P a) (N a)) input encUnary := by
  unfold Cslib.Crypto.MLKEM.encWidth
  have hk : ComputableInPolyTime (fun a => (P a).k) input encUnary := by fun_prop
  have h₁ : ComputableInPolyTime (fun a => (P a).n * (2 * (P a).η₁)) input encUnary := by fun_prop
  have h₂ : ComputableInPolyTime (fun a => (P a).n * (2 * (P a).η₂)) input encUnary := by fun_prop
  simpa only [decide_eq_true_eq] using ComputableInPolyTime.ite' (hN.unary_lt' hk) h₁ h₂

/-- Key-generation noise with computed parameters and seed. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.keyNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {σ : α → List Bool}
    (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hσ : ComputableInPolyTime σ input encBits) :
    ComputableInPolyTime (fun a => keyNoise (P a) F (σ a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.keyNoise
  exact ComputableInPolyTime.expandNoise hP hF hσ (by fun_prop) (by fun_prop)

/-- Encryption coins with computed parameters and seed. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.encNoise {P : α → Params}
    {F : List Bool → List Bool → List Bool} {r : α → List Bool}
    (hP : ComputableInPolyTime P input encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => encNoise (P a) F (r a)) input encBits := by
  unfold Cslib.Crypto.MLKEM.encNoise
  exact ComputableInPolyTime.expandNoise hP hF hr (by fun_prop)
    (ComputableInPolyTime.encWidth (hP.comp (ComputableInPolyTime.fst input encUnary))
      (ComputableInPolyTime.snd input encUnary))

end PolyTime

/-- **K-PKE with seed expansion is an efficient word-level family** whenever its parameters are
computable in polynomial time from the unary security parameter and `F` is evaluated in
polynomial time. -/
theorem kpkePRF_isEfficient {P : ℕ → Params} {F : List Bool → List Bool → List Bool}
    (hP : ComputableInPolyTime P encUnary encParams)
    (hF : ComputableInPolyTime (fun pair : List Bool × List Bool => F pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    (kpkePRF P F).IsEfficient where
  msgLen := (kpke_isEfficient hP).msgLen
  coinLen := ComputableInPolyTime.id'
  ctLen := (kpke_isEfficient hP).ctLen
  keyGen := by
    change IsPPTOn encUnary (encPair encBits encBits) fun κ => keyGenPRFWord (P κ) F κ
    unfold keyGenPRFWord
    have hA := isPPTOn_sampleMatrixResidues.preprocess (hP.prod ComputableInPolyTime.id')
    refine hA.bind_with ((isPPTOn_sampleList.preprocess
      (ComputableInPolyTime.fst encUnary encMatrixResidues)).bind_with ?_)
    let E := encPair (encPair encUnary encMatrixResidues) encBits
    have hP' : ComputableInPolyTime (fun y : (ℕ × List (List (List ℕ))) × List Bool => P y.1.1) E
        encParams := hP.comp (by fun_prop)
    have hnoise := ComputableInPolyTime.keyNoise hP' hF
      (by fun_prop : ComputableInPolyTime
        (fun y : (ℕ × List (List (List ℕ))) × List Bool => y.2) E encBits)
    have hL : ComputableInPolyTime
        (fun y : (ℕ × List (List (List ℕ))) × List Bool =>
          (P y.1.1).k * ((P y.1.1).n * (2 * (P y.1.1).η₁))) E encUnary := by fun_prop
    exact (ComputableInPolyTime.keyWords hP' (by fun_prop)
      (ComputableInPolyTime.bitsTakeWithInput hnoise hL)
      (ComputableInPolyTime.bitsDropWithInput hnoise hL)).isPPTOn
  encDet := by
    change ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool =>
      encDetWord (P x.1) x.2.1 x.2.2.1 (encNoise (P x.1) F x.2.2.2)) encEncDetInput encBits
    have hPx : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool × List Bool => P x.1)
        encEncDetInput encParams := hP.comp (by fun_prop)
    exact ComputableInPolyTime.encDetWord hPx (by fun_prop) (by fun_prop)
      (ComputableInPolyTime.encNoise hPx hF (by fun_prop))
  dec := (kpke_isEfficient hP).dec

end Cslib.Crypto.MLKEM
