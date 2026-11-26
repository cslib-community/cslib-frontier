/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform
public import CslibFrontier.Crypto.Computational.Encryption.NonceBased
public import CslibFrontier.Crypto.Computational.Encryption.SymmetricCPA
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Foundations.Data.BitString.Counter
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Nonce-based counter mode and Theorem 5.6

Nonce-based counter mode ([BonehShoup2023], Section 5.5.2, printed pp. 203–204) recasts the
randomized counter-mode cipher of Section 5.4.2 (`ctrWordKeystream` in
`CslibFrontier.Crypto.Computational.Encryption.CTRMode.Uniform`) to encrypt a sequence of `n`-bit
blocks `m[0], …, m[v - 1]` under an `n`-bit PRF key `k` and a unique nonce `N` with zero ciphertext
expansion. Both variants below share the deterministic constructor `nonceStreamCipher family n toIV`
and differ only in the nonce-to-initial-counter map `toIV`:
* As [BonehShoup2023] observes on printed p. 203, using the nonce directly as the initial counter
  `x := N` (`unscaledNonceCTRCipher`, `nonce ↦ nonce`) fails for multi-block messages because two
  distinct nonces can yield overlapping counter intervals `{x₁, …, x₁ + ℓ - 1}` and
  `{x₂, …, x₂ + ℓ - 1}` and reuse keystream bits (for instance, in our concrete attack below,
  nonces `0` and `1` on 2-block messages both evaluate `F(k, 1)`).
* Instead, when `ℓ = 2 ^ (n - s)` divides `2 ^ n` (`s ≤ n`), the nonce space has size
  `2 ^ n / ℓ = 2 ^ s` (`s`-bit nonces) and `nonceCTRCipher` translates `nonce` to the scaled
  initial counter `nonceCTRCounter n s nonce 0` (`BitString.lowBits (n - s) 0 ++ nonce`,
  representing `x := N · ℓ`). At block offset `j < 2 ^ (n - s)`, `ctrWordCounter` from that initial
  value equals `nonceCTRCounter n s nonce j` (`ctrWordCounter_nonceCTRCounter_zero`), whose
  little-endian value is `N · ℓ + j` (`lsbValue_nonceCTRCounter`).

1. **Construction, correctness, and polynomial-time algorithms (`nonceCTRCounter`,
   `nonceStreamCipher`, `nonceCTRCipher`, `nonceCTRValid`, `nonceCTRValidNonce`)**:
   `nonceStreamCipher family n toIV` XORs messages with `ctrWordKeystream` from `toIV nonce` and
   satisfies `NonceCipher.Correct` unconditionally (`correct_nonceStreamCipher`). Both encryption
   and decryption of `nonceCTRCipher` are computable in deterministic polynomial time whenever
   `family` and `nonceLen` are (`computableInPolyTime_encrypt_nonceCTRCipher`,
   `computableInPolyTime_decrypt_nonceCTRCipher`).
2. **Exact reduction and CPA security (`nonceCTRToPRF`, `isOraclePPT_nonceCTRToPRF`,
   `advantage_cpaExperiment_nonceCTRCipher_eq_two_mul`, `PseudorandomFunction.indcpa_nonceCTR`)**
   ([BonehShoup2023], Theorem 5.6, printed pp. 203–204, and inequality `(5.32)`, printed p. 204):
   [BonehShoup2023] leaves the proof of Theorem 5.6 as an exercise (p. 204), noting that it adapts
   the proof of Theorem 5.3 (p. 203) with `B` an elementary wrapper around `A` (p. 204). Here
   `nonceCTRToPRF nonceLen A` samples a uniform hidden bit `b`, simulates the stateful CPA word
   challenger for `A` via `ctrKeystreamQueries` against its external function oracle, and outputs
   whether `ok && guess` matches `b`. Against a uniform random function, distinct nonces and
   `blocks ≤ 2 ^ (n - nonceLen n)` make every counter query fresh, so `ok && guess` is independent
   of `b` and the distinguisher outputs `true` with probability `1 / 2`. Because Attack Game 5.3's
   two-world CPA advantage (`2 · nCPAadv*` by `(5.30)`, printed p. 202) agrees with
   `Game.advantage`, this yields the exact identity
   $$\mathrm{Adv}_{\mathrm{nCPA}}(A, \mathcal{E}) = 2 \cdot \mathrm{Adv}_{\mathrm{PRF}}(B_A, F),$$
   whose `.le` direction is `(5.32)` (printed p. 204), and hence `NonceCipher.INDCPA` for every
   uniform `PseudorandomFunction`.
3. **Counter-overlap separation for unscaled nonces (`unscaledNonceCTRCipher`,
   `unscaledNonceCTRAdversary`, `isOraclePPT_unscaledNonceCTRAdversary`,
   `advantage_cpaExperiment_unscaledNonceCTRAdversary`, `not_indcpa_unscaledNonceCTRCipher`)**:
   instantiating the overlapping-interval failure noted in [BonehShoup2023], Section 5.5.2 (printed
   p. 203), our concrete 2-query uniform strict `IsOraclePPT` distinguisher
   `unscaledNonceCTRAdversary` queries nonces `0` and `1` on 2-block messages (under
   `blockPairValid` with no block cap) to achieve CPA advantage `1` for every `n ≥ 1`, refuting
   `NonceCipher.INDCPA` for `unscaledNonceCTRCipher`.

## Main definitions

* `Cslib.Crypto.nonceCTRCounter`: little-endian block counter `N · 2 ^ (n - s) + j`.
* `Cslib.Crypto.nonceStreamCipher`, `Cslib.Crypto.nonceCTRCipher`,
  `Cslib.Crypto.unscaledNonceCTRCipher`: deterministic counter-mode stream cipher parameterized by
  the nonce-to-counter map, and its scaled (`x := N · ℓ`) and unscaled (`x := N`) specializations.
* `Cslib.Crypto.nonceCTRValid`, `Cslib.Crypto.nonceCTRValidNonce`: whole-block message-pair
  predicate (`blocks ≤ 2 ^ (n - nonceLen n)`) and `nonceLen n`-bit nonce predicate.
* `Cslib.Crypto.nonceCTRToPRF`: single-distinguisher PRF wrapper adapting the Theorem 5.3 reduction
  to Theorem 5.6.
* `Cslib.Crypto.unscaledNonceCTRAdversary`: concrete 2-query counter-overlap distinguisher.

## Main results

* `Cslib.Crypto.lsbValue_nonceCTRCounter`, `Cslib.Crypto.ctrWordCounter_nonceCTRCounter_zero`:
  little-endian value `lsbValue nonce * 2 ^ (n - s) + j` and agreement of `ctrWordCounter` from the
  scaled initial counter with `nonceCTRCounter` below `2 ^ (n - s)`.
* `Cslib.Crypto.correct_nonceStreamCipher`: decryption inverts encryption for every
  nonce-to-counter map.
* `Cslib.Crypto.computableInPolyTime_encrypt_nonceCTRCipher`,
  `Cslib.Crypto.computableInPolyTime_decrypt_nonceCTRCipher`: polynomial-time efficiency of
  encryption and decryption.
* `Cslib.Crypto.isOraclePPT_nonceCTRToPRF`: uniform strict oracle-PPT certificate for the PRF
  reduction.
* `Cslib.Crypto.advantage_cpaExperiment_nonceCTRCipher_eq_two_mul`: exact CPA-to-PRF advantage
  identity whose `.le` direction is `(5.32)` (printed p. 204).
* `Cslib.Crypto.PseudorandomFunction.indcpa_nonceCTR`: nonce-based counter mode satisfies
  `NonceCipher.INDCPA` for every `PseudorandomFunction` (Theorem 5.6).
* `Cslib.Crypto.isOraclePPT_unscaledNonceCTRAdversary`,
  `Cslib.Crypto.advantage_cpaExperiment_unscaledNonceCTRAdversary`,
  `Cslib.Crypto.not_indcpa_unscaledNonceCTRCipher`: certified counter-overlap attack on unscaled
  nonce-CTR.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.4.2 and Theorem 5.3 (printed pp. 189, 191–192), Section 5.5 (Attack Game 5.3,
  Definition 5.3, and `(5.30)`, printed p. 202), and Section 5.5.2 (nonce-based counter mode,
  counter-overlap failure of unscaled nonces, Theorem 5.6, and `(5.32)`, printed pp. 203–204).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Nonce-based counter mode -/

/-- The `j`-th counter input of nonce-based counter mode at block width `n` and nonce width `s`
([BonehShoup2023], Section 5.5.2, printed p. 203): the `(n - s)`-bit little-endian offset `j`
followed by `nonce`, representing `lsbValue nonce * 2 ^ (n - s) + j` when `j < 2 ^ (n - s)`. -/
@[expose]
def nonceCTRCounter (n s : ℕ) (nonce : List Bool) (j : ℕ) : List Bool :=
  BitString.lowBits (n - s) j ++ nonce

/-- When `s ≤ n` and `nonce` has `s` bits, `nonceCTRCounter n s nonce j` has `n` bits. -/
@[simp]
theorem length_nonceCTRCounter {n s : ℕ} (hs : s ≤ n) {nonce : List Bool}
    (hnonce : nonce.length = s) (j : ℕ) :
    (nonceCTRCounter n s nonce j).length = n := by
  simp only [nonceCTRCounter, List.length_append, BitString.length_lowBits, hnonce]
  omega

/-- Little-endian numeric value of `nonceCTRCounter n s nonce j` for `j < 2 ^ (n - s)`, matching
`x = N · ℓ + j` with `ℓ = 2 ^ (n - s)` ([BonehShoup2023], Section 5.5.2, printed p. 203). -/
theorem lsbValue_nonceCTRCounter {n s : ℕ} (nonce : List Bool) {j : ℕ} (hj : j < 2 ^ (n - s)) :
    BitString.lsbValue (nonceCTRCounter n s nonce j) =
      BitString.lsbValue nonce * 2 ^ (n - s) + j := by
  rw [nonceCTRCounter, BitString.lsbValue_append, BitString.length_lowBits,
    BitString.lsbValue_lowBits hj]
  ring

/-- For an `s`-bit nonce (`s ≤ n`) and block offset `j < 2 ^ (n - s)`, advancing
`ctrWordCounter n` from the scaled initial counter `nonceCTRCounter n s nonce 0` (`x = N · ℓ`)
produces `nonceCTRCounter n s nonce j` (`N · ℓ + j`). -/
theorem ctrWordCounter_nonceCTRCounter_zero {n s : ℕ} (hs : s ≤ n) {nonce : List Bool}
    (hnonce : nonce.length = s) {j : ℕ} (hj : j < 2 ^ (n - s)) :
    ctrWordCounter n (nonceCTRCounter n s nonce 0) j = nonceCTRCounter n s nonce j := by
  rw [ctrWordCounter, lsbValue_nonceCTRCounter nonce (Nat.two_pow_pos (n - s)), add_zero,
    ← lsbValue_nonceCTRCounter nonce hj]
  simpa only [length_nonceCTRCounter hs hnonce j] using
    BitString.lowBits_lsbValue (nonceCTRCounter n s nonce j)

/-- XOR `msg` with `stream` truncated or zero-padded to `msg.length`, preserving `msg.length` for
all inputs. -/
private def xorWithStream (msg stream : List Bool) : List Bool :=
  List.zipWith Bool.xor msg
    (stream.take msg.length ++ List.replicate (msg.length - stream.length) false)

private theorem length_xorWithStream (msg stream : List Bool) :
    (xorWithStream msg stream).length = msg.length := by
  simp only [xorWithStream, List.length_zipWith, List.length_append, List.length_take,
    List.length_replicate]
  omega

private theorem xorWithStream_self (msg stream : List Bool) :
    xorWithStream (xorWithStream msg stream) stream = msg := by
  nth_rw 1 [xorWithStream]
  rw [length_xorWithStream, xorWithStream]
  exact BitString.zipWith_xor_self_right msg _ (by simp; omega)

private theorem xorWithStream_eq_zipWith {msg stream : List Bool} (h : stream.length = msg.length) :
    xorWithStream msg stream = List.zipWith Bool.xor msg stream := by
  rw [xorWithStream, List.take_of_length_le h.le, h, Nat.sub_self, List.replicate_zero,
    List.append_nil]

private theorem div_ceil_eq_div_of_mod_eq_zero {m n : ℕ} (h : m % n = 0) :
    (m + n - 1) / n = m / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    rw [show n * q + n - 1 = (n - 1) + n * q by omega, Nat.add_mul_div_left _ _ hn,
      Nat.mul_div_right _ hn, Nat.div_eq_zero_iff.mpr (Or.inr (by omega)), zero_add]

/-- Deterministic nonce-based counter-mode stream cipher at block width `n` under
nonce-to-initial-counter map `toIV`: encrypt (or decrypt) a word of length `len` by XORing it with
`(len + n - 1) / n` blocks of `ctrWordKeystream family n k (toIV nonce)`, truncated or zero-padded
to `len` bits. -/
@[expose]
def nonceStreamCipher (family : List Bool → List Bool → List Bool) (n : ℕ)
    (toIV : List Bool → List Bool) :
    NonceCipher (List Bool) (List Bool) Unit (List Bool) (List Bool) :=
  let mask (k w nonce : List Bool) : List Bool :=
    let stream := ctrWordKeystream family n k (toIV nonce) ((w.length + n - 1) / n)
    List.zipWith Bool.xor w
      (stream.take w.length ++ List.replicate (w.length - stream.length) false)
  { encrypt := fun k m _ nonce => mask k m nonce
    decrypt := fun k c _ nonce => some (mask k c nonce) }

private theorem nonceStreamCipher_encrypt_eq (family : List Bool → List Bool → List Bool)
    (n : ℕ) (toIV : List Bool → List Bool) (k m nonce : List Bool) :
    (nonceStreamCipher family n toIV).encrypt k m () nonce =
      xorWithStream m
        (ctrWordKeystream family n k (toIV nonce) ((m.length + n - 1) / n)) := rfl

private theorem nonceStreamCipher_decrypt_eq (family : List Bool → List Bool → List Bool)
    (n : ℕ) (toIV : List Bool → List Bool) (k c nonce : List Bool) :
    (nonceStreamCipher family n toIV).decrypt k c () nonce =
      some (xorWithStream c
        (ctrWordKeystream family n k (toIV nonce) ((c.length + n - 1) / n))) := rfl

/-- Decryption inverts encryption for `nonceStreamCipher` on all keys, messages, and nonces. -/
theorem correct_nonceStreamCipher (family : List Bool → List Bool → List Bool) (n : ℕ)
    (toIV : List Bool → List Bool) :
    (nonceStreamCipher family n toIV).Correct := by
  intro k m d nonce
  cases d
  rw [nonceStreamCipher_encrypt_eq, nonceStreamCipher_decrypt_eq, length_xorWithStream,
    xorWithStream_self]

/-- Deterministic nonce-based counter-mode cipher ([BonehShoup2023], Section 5.5.2, printed p. 203)
at block width `n` and nonce width `s`: `nonceStreamCipher` under the scaled nonce translation
`nonce ↦ nonceCTRCounter n s nonce 0` (`x := N · ℓ` with `ℓ = 2 ^ (n - s)`). -/
@[expose]
def nonceCTRCipher (family : List Bool → List Bool → List Bool) (n s : ℕ) :
    NonceCipher (List Bool) (List Bool) Unit (List Bool) (List Bool) :=
  nonceStreamCipher family n (fun nonce => nonceCTRCounter n s nonce 0)

/-- Admissible challenge-pair predicate for nonce-based counter mode with nonce-length schedule
`nonceLen` ([BonehShoup2023], Section 5.5.2, printed p. 203): equal-length messages of whole `n`-bit
blocks (`blockPairValid n m₀ m₁`) with block count `m₀.length / n ≤ 2 ^ (n - nonceLen n)`. -/
@[expose]
def nonceCTRValid (nonceLen : ℕ → ℕ) (n : ℕ) (m₀ m₁ : List Bool) : Bool :=
  blockPairValid n m₀ m₁ && decide (m₀.length / n ≤ 2 ^ (n - nonceLen n))

/-- Valid nonce predicate for nonce-based counter mode: `nonce` has `nonceLen n` bits. -/
@[expose]
def nonceCTRValidNonce (nonceLen : ℕ → ℕ) (n : ℕ) (nonce : List Bool) : Bool :=
  nonce.length == nonceLen n

/-! ### Efficiency of the honest algorithms -/

private theorem computableInPolyTime_nonceCTRCounter_zero {α : Type} {input : α ↪ List Bool}
    {n s : α → ℕ} {nonce : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hnonce : ComputableInPolyTime nonce input encBits) :
    ComputableInPolyTime (fun a => nonceCTRCounter (n a) (s a) (nonce a) 0) input encBits := by
  unfold nonceCTRCounter
  have hlow : ComputableInPolyTime (fun a => BitString.lowBits (n a - s a) 0) input encBits :=
    ComputableInPolyTime.bitsLow (by polytime) (ComputableInPolyTime.const 0)
  polytime

private theorem computableInPolyTime_xorWithStream {α : Type} {input : α ↪ List Bool}
    {msg stream : α → List Bool}
    (hmsg : ComputableInPolyTime msg input encBits)
    (hstream : ComputableInPolyTime stream input encBits) :
    ComputableInPolyTime (fun a => xorWithStream (msg a) (stream a)) input encBits := by
  unfold xorWithStream
  polytime

/-- Nonce-based counter-mode encryption is computable in polynomial time on `(n, k, msg, nonce)`. -/
theorem computableInPolyTime_encrypt_nonceCTRCipher {family : List Bool → List Bool → List Bool}
    {nonceLen : ℕ → ℕ}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary) :
    ComputableInPolyTime
      (fun ((n, k, msg, nonce) : ℕ × List Bool × List Bool × List Bool) =>
        (nonceCTRCipher family n (nonceLen n)).encrypt k msg () nonce)
      (encKeyedInput (encPair encBits encBits)) encBits := by
  simp only [nonceCTRCipher, nonceStreamCipher_encrypt_eq]
  refine computableInPolyTime_xorWithStream (by polytime) ?_
  exact computableInPolyTime_ctrWordKeystream hpoly (by polytime) (by polytime)
    (computableInPolyTime_nonceCTRCounter_zero (by polytime) (by polytime) (by polytime))
    (by polytime)

/-- Nonce-based counter-mode decryption is computable in polynomial time on `(n, k, ct, nonce)`. -/
theorem computableInPolyTime_decrypt_nonceCTRCipher {family : List Bool → List Bool → List Bool}
    {nonceLen : ℕ → ℕ}
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary) :
    ComputableInPolyTime
      (fun ((n, k, ct, nonce) : ℕ × List Bool × List Bool × List Bool) =>
        (nonceCTRCipher family n (nonceLen n)).decrypt k ct () nonce)
      (encKeyedInput (encPair encBits encBits)) (encOption encBits) := by
  have henc := computableInPolyTime_encrypt_nonceCTRCipher hpoly hnonceLen
  exact (ComputableInPolyTime.optionSome encBits).comp henc

private theorem computableInPolyTime_nonceCTRValid {nonceLen : ℕ → ℕ}
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {m₀ m₁ : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hm₀ : ComputableInPolyTime m₀ input encBits)
    (hm₁ : ComputableInPolyTime m₁ input encBits) :
    ComputableInPolyTime (fun a => nonceCTRValid nonceLen (n a) (m₀ a) (m₁ a)) input encBool := by
  have heq : (fun a => nonceCTRValid nonceLen (n a) (m₀ a) (m₁ a)) = fun a =>
      blockPairValid (n a) (m₀ a) (m₁ a) &&
        decide (Nat.clog 2 ((m₀ a).length / n a) ≤ n a - nonceLen (n a)) := by
    funext a
    simp only [nonceCTRValid, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  have hclog : ComputableInPolyTime (fun a => Nat.clog 2 ((m₀ a).length / n a)) input encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp (by polytime)
  rw [heq]
  polytime [blockPairValid]

/-! ### The PRF reduction for Theorem 5.6 -/

private def nonceCTRHandler (nonceLen : ℕ → ℕ) (n : ℕ) (b : Bool)
    (request : Unit × List Bool) :
    StateT (Bool × List (List Bool)) (WordOracleComp Unit) (List Bool)
  | (ok, seen) =>
    match NonceCipher.unitCPACodec.decodeQuery request with
    | none => pure ([], (ok, seen))
    | some (pair, _, nonce) =>
      if ok && nonceCTRValid nonceLen n pair.msg₀ pair.msg₁ &&
          nonceCTRValidNonce nonceLen n nonce && decide (nonce ∉ seen) then
        (fun stream =>
          (true :: xorWithStream (pair.select b) stream, (true, nonce :: seen))) <$>
          ctrKeystreamQueries n (nonceCTRCounter n (nonceLen n) nonce 0) (pair.msg₀.length / n)
      else
        pure ([], (false, seen))

private noncomputable def nonceCTRSimView (nonceLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (b : Bool) : OracleDistinguisher :=
  fun n _ => do
    let (guess, ok, _) ←
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (nonceCTRHandler nonceLen n b))
        (adversary n [])).run (true, [])
    return (ok && guess)

/-- Single-distinguisher PRF wrapper for nonce-based counter mode, adapting the bit-guessing
reduction of [BonehShoup2023], Theorem 5.3 (printed pp. 191–192) to Theorem 5.6 (whose proof
[BonehShoup2023], Section 5.5.2, printed pp. 203–204 leaves as an exercise, describing `B` as an
elementary wrapper around `A`): sample a uniform hidden bit `b`, simulate the stateful CPA word
challenger for `adversary` via `ctrKeystreamQueries` against the external function oracle, and
output whether `ok && guess` equals `b`. -/
noncomputable def nonceCTRToPRF (nonceLen : ℕ → ℕ) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n aux => do
    let b ← ProbOracleComp.sample (ProbComp.uniform Bool)
    (· == b) <$> nonceCTRSimView nonceLen adversary b n aux

private theorem nonceCTRHandler_eq_ite (nonceLen : ℕ → ℕ) (n : ℕ) (b : Bool)
    (request : Unit × List Bool) (state : Bool × List (List Bool)) :
    nonceCTRHandler nonceLen n b request state =
      let m₀ := unframe request.2
      let rest := dropFrame request.2
      let m₁ := unframe rest
      let nonce := dropFrame rest
      if frame m₀ ++ frame m₁ ++ nonce == request.2 then
        if state.1 && nonceCTRValid nonceLen n m₀ m₁ &&
            nonceCTRValidNonce nonceLen n nonce && decide (nonce ∉ state.2) then
          (fun stream =>
            (true :: xorWithStream ((MessagePair.mk m₀ m₁).select b) stream,
              (true, nonce :: state.2))) <$>
            ctrKeystreamQueries n (nonceCTRCounter n (nonceLen n) nonce 0) (m₀.length / n)
        else
          pure ([], (false, state.2))
      else
        pure ([], state) := by
  rcases state with ⟨ok, seen⟩
  rcases request with ⟨⟨⟩, word⟩
  unfold nonceCTRHandler
  dsimp only
  cases hdec : NonceCipher.unitCPACodec.decodeQuery ((), word) with
  | none =>
    have hfalse : (frame (unframe word) ++ frame (unframe (dropFrame word)) ++
        dropFrame (dropFrame word) == word) = false :=
      beq_eq_false_iff_ne.mpr fun heq => nomatch hdec.symm.trans
        ((NonceCipher.unitCPACodec.decodeQuery_eq_some_iff ((), word)
          (⟨unframe word, unframe (dropFrame word)⟩, (), dropFrame (dropFrame word))).mpr
          (Prod.ext rfl (by simpa [NonceCipher.unitCPACodec, List.append_assoc] using heq)))
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
  | some q =>
    rcases q with ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
    have hword : frame m₀ ++ (frame m₁ ++ nonce) = word := by
      simpa [NonceCipher.unitCPACodec, List.append_assoc] using congrArg Prod.snd
        ((NonceCipher.unitCPACodec.decodeQuery_eq_some_iff ((), word) (⟨m₀, m₁⟩, (), nonce)).mp
          hdec)
    have hrest : dropFrame word = frame m₁ ++ nonce := by rw [← hword, dropFrame_frame_append]
    have hm₀ : unframe word = m₀ := by rw [← hword, unframe_frame_append]
    have hm₁ : unframe (dropFrame word) = m₁ := by rw [hrest, unframe_frame_append]
    have hnonce : dropFrame (dropFrame word) = nonce := by rw [hrest, dropFrame_frame_append]
    have htrue : (frame m₀ ++ frame m₁ ++ nonce == word) = true :=
      beq_iff_eq.mpr (by simpa [List.append_assoc] using hword)
    simp only [hm₀, hm₁, hnonce, htrue, ↓reduceIte]

private abbrev HandlerCall :=
  ((ℕ × List Bool) × Bool) × ((Unit × List Bool) × (Bool × List (List Bool)))

private abbrev encHandlerCallNonceCTR : HandlerCall ↪ List Bool :=
  encPair (encPair (encPair encUnary encBits) encBool)
    (encPair (encPair (encFinEnum Unit) encBits) (encPair encBool (encList encBits)))

private theorem isOraclePPTOn_nonceCTRHandler {nonceLen : ℕ → ℕ}
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary) :
    IsOraclePPTOn encHandlerCallNonceCTR (encPair encBits (encPair encBool (encList encBits)))
      (fun x : HandlerCall => nonceCTRHandler nonceLen x.1.1.1 x.1.2 x.2.1 x.2.2) := by
  simp_rw [nonceCTRHandler_eq_ite]
  have hm₀ : ComputableInPolyTime (fun x : HandlerCall => unframe x.2.1.2)
      encHandlerCallNonceCTR encBits := by fun_prop
  have hm₁ : ComputableInPolyTime (fun x : HandlerCall => unframe (dropFrame x.2.1.2))
      encHandlerCallNonceCTR encBits := by fun_prop
  have hnonce : ComputableInPolyTime (fun x : HandlerCall => dropFrame (dropFrame x.2.1.2))
      encHandlerCallNonceCTR encBits := by fun_prop
  have hcondOuter : ComputableInPolyTime
      (fun x : HandlerCall =>
        frame (unframe x.2.1.2) ++ frame (unframe (dropFrame x.2.1.2)) ++
          dropFrame (dropFrame x.2.1.2) == x.2.1.2)
      encHandlerCallNonceCTR encBool := by
    have henc3 : ComputableInPolyTime
        (fun x : HandlerCall =>
          frame (unframe x.2.1.2) ++ frame (unframe (dropFrame x.2.1.2)) ++
            dropFrame (dropFrame x.2.1.2))
        encHandlerCallNonceCTR encBits := by
      simpa only [encPair_apply, encBits_apply, List.append_assoc] using
        ComputableInPolyTime.encoding_comp (hm₀.prod (hm₁.prod hnonce))
    simpa only [beq_eq_decide] using ComputableInPolyTime.decide_eq' henc3 (by fun_prop)
  have hvalid := computableInPolyTime_nonceCTRValid hnonceLen (n := fun x : HandlerCall => x.1.1.1)
    (by fun_prop) hm₀ hm₁
  refine IsOraclePPTOn.cond hcondOuter
    (IsOraclePPTOn.cond (by unfold nonceCTRValidNonce; fun_prop) ?_ (by ppt)) (by ppt)
  refine (isOraclePPTOn_ctrKeystreamQueries (by fun_prop)
    (computableInPolyTime_nonceCTRCounter_zero (by fun_prop) (by fun_prop) hnonce)
    (by fun_prop)).map_with ?_
  simp only [MessagePair.select, Bool.cond_eq_ite]
  exact (ComputableInPolyTime.bitsCons (.const true)
    (computableInPolyTime_xorWithStream (by fun_prop) (by fun_prop))).prod (by fun_prop)

/-- **Efficiency of the Theorem 5.6 reduction.** When `nonceLen` is computable in polynomial time
in unary and `adversary` is uniform strict oracle PPT, `nonceCTRToPRF nonceLen adversary` is
uniform strict oracle PPT. -/
theorem isOraclePPT_nonceCTRToPRF {nonceLen : ℕ → ℕ} {adversary : OracleDistinguisher}
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary)
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (nonceCTRToPRF nonceLen adversary) := by
  have hhandler := isOraclePPTOn_nonceCTRHandler hnonceLen
  have hrun : IsOraclePPTOn (encPair (encPair encUnary encBits) encBool)
      (encPair encBool (encPair encBool (encList encBits)))
      (fun cb : (ℕ × List Bool) × Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (nonceCTRHandler nonceLen cb.1.1 cb.2))
          (adversary cb.1.1 [])).run (true, [])) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun cb : (ℕ × List Bool) × Bool => (cb.1.1, ([] : List Bool)))
      (initial := fun _ => (true, ([] : List (List Bool))))
      (resources := fun _ word => 2 * word.length + 2)
      (by polytime) hhandler (ComputableInPolyTime.const _)
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro cb ⟨⟨⟩, word⟩ ⟨ok, seen⟩ _ result hresult
    unfold nonceCTRHandler at hresult
    cases hdec : NonceCipher.unitCPACodec.decodeQuery ((), word) with
    | none =>
      simp only [hdec] at hresult
      rw [OracleComp.eq_of_mem_supportWith_pure hresult]
      exact ⟨trivial, by simp, by dsimp only; omega⟩
    | some q =>
      rcases q with ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
      simp only [hdec] at hresult
      have hword : frame m₀ ++ frame m₁ ++ nonce = word :=
        congrArg Prod.snd ((NonceCipher.unitCPACodec.decodeQuery_eq_some_iff ((), word) _).mp hdec)
      have hlen : 2 * m₀.length + 2 * m₁.length + nonce.length + 2 = word.length := by
        simp [← hword, length_frame]; omega
      split_ifs at hresult
      · obtain ⟨stream, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        have hselLen : ((MessagePair.mk m₀ m₁).select cb.2).length ≤ m₀.length + m₁.length := by
          cases cb.2 <;> simp [MessagePair.select]
        refine ⟨trivial, by simp only [List.length_cons, length_xorWithStream]; omega, ?_⟩
        enc_len [List.length_singleton]
      · rw [OracleComp.eq_of_mem_supportWith_pure hresult]
        exact ⟨trivial, by simp, by enc_len [List.length_singleton]⟩
  ppt [nonceCTRToPRF, nonceCTRSimView]

/-! ### Real and ideal PRF worlds and Theorem 5.6 -/

private theorem eval_prfRealGame_nonceCTRSimView {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {nonceLen : ℕ → ℕ} {n : ℕ} (adversary : OracleDistinguisher) (b : Bool) :
    ProbComp.eval (prfRealGame id family (nonceCTRSimView nonceLen adversary b) n) =
      ProbComp.eval ((nonceCTRCipher family n (nonceLen n)).cpaExperiment
        (BitString.sampleList n) (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n)
        (NonceCipher.unitCPACodec.adapt (adversary n [])) b) := by
  rw [NonceCipher.eval_cpaExperiment]
  simp only [prfRealGame, id_eq, nonceCTRSimView, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  rw [BitString.eval_sampleList] at hk
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  rw [NonceCipher.unitCPACodec.runWith_adapt, ← PMF.bind_pure_comp]
  congr 2
  funext request ⟨ok, seen⟩
  dsimp only [StateT.run]
  rw [show (fun req : Unit × List Bool => PMF.pure (prfOracle family n k req.2)) =
      (fun req => ProbComp.eval (pure (prfOracle family n k req.2))) from rfl,
    ← ProbOracleComp.eval_run_eq_evalWith]
  unfold nonceCTRHandler OracleCodec.wordOracle NonceCipher.cpaOracle
  cases hdec : NonceCipher.unitCPACodec.decodeQuery request with
  | none =>
    rw [ProbOracleComp.run_pure, ProbComp.eval_pure]
    rfl
  | some q =>
    rcases q with ⟨pair, ⟨⟩, nonce⟩
    dsimp only
    by_cases hcond : (ok && nonceCTRValid nonceLen n pair.msg₀ pair.msg₁ &&
        nonceCTRValidNonce nonceLen n nonce && decide (nonce ∉ seen)) = true
    · rw [ite_eq_left hcond, ProbOracleComp.run_map, run_ctrKeystreamQueries hlen hkLen,
        map_pure, ProbComp.eval_pure]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have hpair := hcond.1.1.2
      simp only [nonceCTRValid, blockPairValid, Bool.and_eq_true, beq_iff_eq] at hpair
      rcases hpair with ⟨⟨hlenPair, hmod⟩, _⟩
      have hselMod : (pair.select b).length % n = 0 := by
        cases b <;> simp [MessagePair.select, ← hlenPair, hmod]
      have hselDiv : ((pair.select b).length + n - 1) / n = pair.msg₀.length / n := by
        rw [div_ceil_eq_div_of_mod_eq_zero hselMod]
        cases b <;> simp [MessagePair.select, hlenPair]
      dsimp only [Functor.map, StateT.map]
      simp [hcond.1.1.1, hcond.1.1.2, hcond.1.2, hcond.2, NonceCipher.unitCPACodec,
        nonceCTRCipher, nonceStreamCipher_encrypt_eq, hselDiv]
    · rw [ite_eq_right hcond, ProbOracleComp.run_pure, ProbComp.eval_pure]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      dsimp only [Functor.map, StateT.map]
      simp [hcond, NonceCipher.unitCPACodec]

private noncomputable def nonceCTRIdealOracle (nonceLen : ℕ → ℕ) (n : ℕ)
    (request : Unit × List Bool) : StateT (Bool × List (List Bool)) PMF (List Bool)
  | (ok, seen) =>
    match NonceCipher.unitCPACodec.decodeQuery request with
    | none => PMF.pure ([], (ok, seen))
    | some (pair, _, nonce) =>
      if ok && nonceCTRValid nonceLen n pair.msg₀ pair.msg₁ &&
          nonceCTRValidNonce nonceLen n nonce && decide (nonce ∉ seen) then
        (BitString.uniformList pair.msg₀.length).map fun ct => (true :: ct, (true, nonce :: seen))
      else
        PMF.pure ([], (false, seen))

private theorem uniformList_map_xorWithStream (msg : List Bool) :
    (BitString.uniformList msg.length).map (xorWithStream msg) =
      BitString.uniformList msg.length := by
  let f : List Bool → List Bool := fun stream =>
    if stream.length = msg.length then List.zipWith Bool.xor msg stream else stream
  have hinv : Function.Involutive f := by
    intro stream
    dsimp only [f]
    by_cases h : stream.length = msg.length
    · have hzip : (List.zipWith Bool.xor msg stream).length = msg.length := by simp [h]
      simp [h, hzip, BitString.zipWith_xor_self_left msg stream h.symm]
    · simp [h]
  have hf : (BitString.uniformList msg.length).map f = BitString.uniformList msg.length :=
    BitString.uniformList_map_of_bijective f hinv.bijective
      (fun stream => by dsimp only [f]; split_ifs with h <;> simp [h]) msg.length
  refine Eq.trans ?_ hf
  simp only [PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun stream hstream => ?_
  have hlen := BitString.length_of_mem_support_uniformList hstream
  simp [f, hlen, xorWithStream_eq_zipWith hlen]

private theorem lazyRandomFunctionOracle_of_none {n : ℕ} {query : List Bool} (hq : query.length = n)
    {cache : RandomOracle.Cache (fun _ : BitString n => BitString n)}
    (hnone : cache (BitString.ofList n query) = none) :
    lazyRandomFunctionOracle n n query cache =
      (PMF.uniformOfFintype (BitString n)).map fun y =>
        (List.ofFn y, Function.update cache (BitString.ofList n query) (some y)) := by
  classical
  change (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString n))))
      (randomFunctionQuery n query)).run cache = _
  rw [← ProbOracleComp.runWith_eq_run_interpret, randomFunctionQuery, ite_eq_left hq,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    RandomOracle.answer_of_none _ _ _ hnone, PMF.map_comp]
  rfl

private theorem runWith_ctrKeystreamQueries_lazy {n s : ℕ} (hs : s ≤ n)
    {nonce : List Bool} (hnonce : nonce.length = s) {seen : List (List Bool)}
    (hfresh : nonce ∉ seen) {blocks : ℕ} (hblocks : blocks ≤ 2 ^ (n - s))
    {cache : RandomOracle.Cache (fun _ : BitString n => BitString n)}
    (hcache : ∀ x : BitString n, cache x ≠ none → (List.ofFn x).drop (n - s) ∈ seen) :
    let run := ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
      (ctrKeystreamQueries n (nonceCTRCounter n s nonce 0) blocks) cache
    (∀ res ∈ run.support,
      ∀ x : BitString n, res.2 x ≠ none → (List.ofFn x).drop (n - s) ∈ nonce :: seen) ∧
      run.map Prod.fst = BitString.uniformList (blocks * n) := by
  classical
  let iv := nonceCTRCounter n s nonce 0
  have hloop : ∀ k ≤ blocks,
      let runK := ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
        (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache
      (∀ res ∈ runK.support, res.1.1 = k ∧ res.1.2.length = k * n ∧
        ∀ x : BitString n, res.2 x ≠ none →
          (List.ofFn x).drop (n - s) ∈ seen ∨
            ((List.ofFn x).drop (n - s) = nonce ∧
              BitString.lsbValue ((List.ofFn x).take (n - s)) < k)) ∧
        runK.map (fun res => res.1.2) = BitString.uniformList (k * n) := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      rw [OracleComp.iterate_zero, ProbOracleComp.runWith_pure]
      refine ⟨fun res hres => ?_, by simp⟩
      rw [PMF.mem_support_pure_iff] at hres
      subst hres
      exact ⟨rfl, by simp, fun x hx => Or.inl (hcache x hx)⟩
    | succ k ih =>
      obtain ⟨hsupp, hlaw⟩ := ih (Nat.le_of_succ_le hk)
      have hkPow : k < 2 ^ (n - s) := lt_of_lt_of_le (Nat.lt_succ_self k) (hk.trans hblocks)
      let xk := BitString.ofList n (nonceCTRCounter n s nonce k)
      have hxkOfFn : List.ofFn xk = BitString.lowBits (n - s) k ++ nonce :=
        BitString.ofFn_ofList (length_nonceCTRCounter hs hnonce k)
      have hxkDrop : (List.ofFn xk).drop (n - s) = nonce := by
        rw [hxkOfFn]; exact List.drop_left' (BitString.length_lowBits (n - s) k)
      have hxkTake : BitString.lsbValue ((List.ofFn xk).take (n - s)) = k := by
        rw [hxkOfFn, List.take_left' (BitString.length_lowBits (n - s) k),
          BitString.lsbValue_lowBits hkPow]
      have hstep_of_supp : ∀ mid ∈ (ProbOracleComp.runWith
          (fun req => lazyRandomFunctionOracle n n req.2)
          (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache).support,
          ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
            (ctrKeystreamStep n iv mid.1) mid.2 =
          (PMF.uniformOfFintype (BitString n)).map fun y =>
            ((k + 1, mid.1.2 ++ List.ofFn y), Function.update mid.2 xk (some y)) := by
        intro mid hmid
        obtain ⟨hidx, _, hmidCache⟩ := hsupp mid hmid
        have hnone : mid.2 xk = none := by
          by_contra hne
          rcases hmidCache xk hne with hmem | ⟨_, hlt⟩
          · exact hfresh (hxkDrop ▸ hmem)
          · exact Nat.lt_irrefl k (hxkTake ▸ hlt)
        rcases mid with ⟨⟨idx, stream⟩, cacheMid⟩
        dsimp only at hidx hnone ⊢
        subst idx
        simp only [ctrKeystreamStep, iv, ctrWordCounter_nonceCTRCounter_zero hs hnonce hkPow,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
          lazyRandomFunctionOracle_of_none (length_nonceCTRCounter hs hnonce k) hnone,
          PMF.map_comp, Function.comp_def]
        refine congrArg ((PMF.uniformOfFintype (BitString n)).map ·) (funext fun y => ?_)
        simp [xk, Prod.map, List.take_of_length_le (List.length_ofFn (f := y)).le]
      dsimp only
      rw [OracleComp.iterate_succ, ProbOracleComp.runWith_bind]
      refine ⟨fun res hres => ?_, ?_⟩
      · rw [PMF.mem_support_bind_iff] at hres
        obtain ⟨mid, hmid, hresMid⟩ := hres
        rw [hstep_of_supp mid hmid, PMF.mem_support_map_iff] at hresMid
        obtain ⟨y, -, rfl⟩ := hresMid
        obtain ⟨_, hstreamLen, hmidCache⟩ := hsupp mid hmid
        refine ⟨rfl, by simp [hstreamLen, Nat.succ_mul], fun x hx => ?_⟩
        dsimp only at hx
        by_cases hxx : x = xk
        · subst hxx
          exact Or.inr ⟨hxkDrop, hxkTake ▸ Nat.lt_succ_self k⟩
        · rw [Function.update_of_ne hxx] at hx
          exact (hmidCache x hx).imp_right fun ⟨hd, hlt⟩ => ⟨hd, Nat.lt_succ_of_lt hlt⟩
      · rw [PMF.map_bind, Nat.succ_mul, BitString.uniformList_add, ← hlaw, PMF.bind_map]
        refine PMF.bind_congr_on_support _ _ _ fun mid hmid => ?_
        rw [Function.comp_apply, hstep_of_supp mid hmid]
        simp [BitString.uniformList, PMF.map_comp, Function.comp_def]
  obtain ⟨hsupp, hlaw⟩ := hloop blocks le_rfl
  dsimp only [ctrKeystreamQueries, iv]
  rw [ProbOracleComp.runWith_map]
  refine ⟨fun res hres x hx => ?_, by
    simpa only [PMF.map_comp, Function.comp_def, Prod.map] using hlaw⟩
  rw [PMF.mem_support_map_iff] at hres
  obtain ⟨mid, hmid, rfl⟩ := hres
  rcases (hsupp mid hmid).2.2 x hx with hmem | ⟨hd, -⟩
  · exact List.mem_cons_of_mem _ hmem
  · exact hd ▸ List.mem_cons_self

private theorem eval_prfIdealGame_nonceCTRSimView {nonceLen : ℕ → ℕ} {n : ℕ} (hs : nonceLen n ≤ n)
    (adversary : OracleDistinguisher) (b : Bool) :
    ProbComp.eval (prfIdealGame id id (nonceCTRSimView nonceLen adversary b) n) =
      (ProbOracleComp.runWith (nonceCTRIdealOracle nonceLen n) (adversary n []) (true, [])).map
        fun (guess, ok, _) => ok && guess := by
  classical
  rw [prfIdealGame_eq_lazy]
  simp only [id_eq, nonceCTRSimView, runWith_norm, pmf_norm]
  let inv : (Bool × List (List Bool)) ×
      RandomOracle.Cache (fun _ : BitString n => BitString n) → Prop :=
    fun state =>
      ∀ x : BitString n, state.2 x ≠ none → (List.ofFn x).drop (n - nonceLen n) ∈ state.1.2
  let jointOracle : Unit × List Bool →
      StateT ((Bool × List (List Bool)) × RandomOracle.Cache (fun _ : BitString n => BitString n))
        PMF (List Bool) :=
    fun q state =>
      (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
        ((nonceCTRHandler nonceLen n b q).run state.1) state.2).map
        fun ⟨⟨a, s'⟩, c'⟩ => (a, s', c')
  have hstep_inv_and_law : ∀ q state, inv state →
      (∀ a state', (a, state') ∈ (jointOracle q state).support → inv state') ∧
      (jointOracle q state).map (fun (a, state') => (a, state'.1)) =
        nonceCTRIdealOracle nonceLen n q state.1 := by
    rintro request ⟨⟨ok, seen⟩, cache⟩ hinv
    dsimp only [jointOracle, nonceCTRHandler, nonceCTRIdealOracle, StateT.run]
    cases hdec : NonceCipher.unitCPACodec.decodeQuery request with
    | none =>
      simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.mem_support_pure_iff,
        Prod.mk.injEq, and_true]
      exact fun _ _ h => h.2.symm ▸ hinv
    | some q =>
      rcases q with ⟨pair, ⟨⟩, nonce⟩
      dsimp only
      split_ifs with hcond
      · simp only [Bool.and_eq_true, nonceCTRValid, blockPairValid, nonceCTRValidNonce,
          beq_iff_eq, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨⟨_, ⟨hlenPair, hmod⟩, hblocks⟩, hnonceLen⟩, hfresh⟩
        obtain ⟨hsuppKs, hlawKs⟩ :=
          runWith_ctrKeystreamQueries_lazy hs hnonceLen hfresh hblocks hinv
        have hselLen : (pair.select b).length = pair.msg₀.length := by
          cases b <;> simp [MessagePair.select, hlenPair]
        have hmulBlocks : pair.msg₀.length / n * n = pair.msg₀.length :=
          Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
        simp only [ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def, Prod.map, id_eq]
        refine ⟨fun a state' hmem => ?_, ?_⟩
        · rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨ksRes, hksRes, ⟨⟩⟩ := hmem
          exact hsuppKs ksRes hksRes
        · trans ((ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
              (ctrKeystreamQueries n (nonceCTRCounter n (nonceLen n) nonce 0)
                (pair.msg₀.length / n)) cache).map Prod.fst).map
              (fun s => (true :: xorWithStream (pair.select b) s, (true, nonce :: seen)))
          · rw [PMF.map_comp]; rfl
          · rw [hlawKs, hmulBlocks]
            conv_rhs => rw [← hselLen, ← uniformList_map_xorWithStream (pair.select b)]
            rw [PMF.map_comp, hselLen]
            rfl
      · simp only [ProbOracleComp.runWith_pure, PMF.pure_map, PMF.mem_support_pure_iff,
          Prod.mk.injEq, and_true]
        exact fun _ _ h => h.2.symm ▸ hinv
  have hsim := ProbOracleComp.runWith_map_state_of_invariant
    jointOracle (nonceCTRIdealOracle nonceLen n) Prod.fst inv
    (fun q s hs a s' hmem => (hstep_inv_and_law q s hs).1 a s' hmem)
    (fun q s hs => (hstep_inv_and_law q s hs).2)
    (adversary n []) ((true, []), fun _ => none) (fun _ hx => (hx rfl).elim)
  have hmap := congrArg (PMF.map fun (guess, ok, _) => ok && guess) hsim
  exact (PMF.bind_pure_comp _ _).trans (by
    simpa only [PMF.map_comp, Function.comp_def, jointOracle] using hmap)

private theorem eval_prfGame_nonceCTRToPRF_eq_bind {nonceLen : ℕ → ℕ}
    (adversary : OracleDistinguisher) (n : ℕ) {α : Type} (setup : ProbComp α)
    (oracleOf : α → Unit × List Bool → List Bool) :
    ProbComp.eval (do
      let x ← setup
      (nonceCTRToPRF nonceLen adversary n []).run fun req => pure (oracleOf x req)) =
    (PMF.uniformOfFintype Bool).bind fun b =>
      (ProbComp.eval (do
        let x ← setup
        (nonceCTRSimView nonceLen adversary b n []).run fun req => pure (oracleOf x req))).map
        (· == b) := by
  simp only [nonceCTRToPRF, ProbComp.eval_uniform, runWith_norm, pmf_norm]
  rw [PMF.bind_comm]

/-- **Exact CPA-to-PRF advantage identity for nonce-based counter mode** (strengthening inequality
`(5.32)` of [BonehShoup2023], Theorem 5.6, printed p. 204, to an equality): for any
length-preserving `family`, parameter `n` with `nonceLen n ≤ n`, and distinguisher `adversary`, the
two-world CPA advantage of `unitCPACodec.adapt (adversary n [])` against
`nonceCTRCipher family n (nonceLen n)` equals twice the PRF advantage of
`nonceCTRToPRF nonceLen adversary`. Applying `.le` gives `(5.32)` directly (Attack Game 5.3's
two-world advantage, printed p. 202, equals `Game.advantage` and is twice the bit-guessing
advantage `(5.30)`). -/
theorem advantage_cpaExperiment_nonceCTRCipher_eq_two_mul
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {nonceLen : ℕ → ℕ} {n : ℕ} (hs : nonceLen n ≤ n) (adversary : OracleDistinguisher) :
    Game.advantage
      (ProbComp.eval ((nonceCTRCipher family n (nonceLen n)).cpaExperiment
        (BitString.sampleList n) (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n)
        (NonceCipher.unitCPACodec.adapt (adversary n [])) false))
      (ProbComp.eval ((nonceCTRCipher family n (nonceLen n)).cpaExperiment
        (BitString.sampleList n) (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n)
        (NonceCipher.unitCPACodec.adapt (adversary n [])) true)) =
    2 * Game.advantage
      (ProbComp.eval (prfRealGame id family (nonceCTRToPRF nonceLen adversary) n))
      (ProbComp.eval (prfIdealGame id id (nonceCTRToPRF nonceLen adversary) n)) := by
  have hreal : ProbComp.eval (prfRealGame id family (nonceCTRToPRF nonceLen adversary) n) =
      (PMF.uniformOfFintype Bool).bind fun b =>
        (ProbComp.eval ((nonceCTRCipher family n (nonceLen n)).cpaExperiment
          (BitString.sampleList n) (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n)
          (NonceCipher.unitCPACodec.adapt (adversary n [])) b)).map (· == b) := by
    rw [prfRealGame, eval_prfGame_nonceCTRToPRF_eq_bind]
    exact congrArg _ (funext fun b =>
      congrArg (PMF.map (· == b)) (eval_prfRealGame_nonceCTRSimView hlen adversary b))
  have hideal : ProbComp.eval (prfIdealGame id id (nonceCTRToPRF nonceLen adversary) n) =
      PMF.uniformOfFintype Bool := by
    rw [prfIdealGame, eval_prfGame_nonceCTRToPRF_eq_bind]
    refine (congrArg (PMF.bind (PMF.uniformOfFintype Bool)) (funext fun b => ?_)).trans
      (Game.uniform_bool_bind_map_beq_const
        ((ProbOracleComp.runWith (nonceCTRIdealOracle nonceLen n)
          (adversary n []) (true, [])).map fun (guess, ok, _) => ok && guess))
    exact congrArg (PMF.map (· == b)) (eval_prfIdealGame_nonceCTRSimView hs adversary b)
  rw [hreal, hideal]
  exact Game.advantage_eq_two_mul_guessingAdvantage_uniform_bool_beq fun b =>
    ProbComp.eval ((nonceCTRCipher family n (nonceLen n)).cpaExperiment
      (BitString.sampleList n) (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n)
      (NonceCipher.unitCPACodec.adapt (adversary n [])) b)

/-- **Nonce-based counter mode is CPA-secure for a pseudorandom function** ([BonehShoup2023],
Section 5.5.2, Theorem 5.6, printed pp. 203–204): in the standard model against uniform strict
oracle-PPT adversaries, if `family` is a `PseudorandomFunction` (`n`-bit keys and `n`-bit inputs to
`n`-bit outputs) and `nonceLen` is computable in polynomial time in unary with `nonceLen n ≤ n`,
then `nonceCTRCipher family n (nonceLen n)` satisfies `NonceCipher.INDCPA` on whole-block message
pairs of at most `ℓ = 2 ^ (n - nonceLen n)` blocks under `nonceLen n`-bit nonces (the power-of-two
case `ℓ ∣ 2 ^ n` noted on printed p. 203). -/
theorem PseudorandomFunction.indcpa_nonceCTR {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) {nonceLen : ℕ → ℕ}
    (hnonceLen : ComputableInPolyTime nonceLen encUnary encUnary)
    (hle : ∀ n, nonceLen n ≤ n) :
    NonceCipher.INDCPA (fun n => nonceCTRCipher family n (nonceLen n))
      BitString.sampleList (nonceCTRValid nonceLen) (nonceCTRValidNonce nonceLen) := by
  intro adversary hadversary
  have hprfA := hprf.secure (nonceCTRToPRF nonceLen adversary)
    (isOraclePPT_nonceCTRToPRF hnonceLen hadversary)
  exact (hprfA.const_mul 2).congr fun n =>
    (advantage_cpaExperiment_nonceCTRCipher_eq_two_mul hprf.length_eq (hle n) adversary).symm

/-! ### Counter-overlap attack on unscaled nonce-based counter mode -/

/-- The unscaled first attempt at nonce-based counter mode ([BonehShoup2023], Section 5.5.2,
printed p. 203): `nonceStreamCipher` under the identity nonce translation `nonce ↦ nonce`
(`x := N`), using the `n`-bit nonce directly as the initial counter of `ctrWordKeystream` without
multiplying by the maximum block count `ℓ`. -/
@[expose]
def unscaledNonceCTRCipher (family : List Bool → List Bool → List Bool) (n : ℕ) :
    NonceCipher (List Bool) (List Bool) Unit (List Bool) (List Bool) :=
  nonceStreamCipher family n (fun nonce => nonce)

/-- Concrete two-query counter-overlap CPA distinguisher against `unscaledNonceCTRCipher`,
instantiating the overlapping-interval observation of [BonehShoup2023], Section 5.5.2, printed
p. 203:
1. Query `(0^(2n), 0^(2n))` under nonce `lowBits n 0` to observe `F(k, 1)` as the second `n`-bit
   ciphertext block.
2. Query `(0^(2n), 1^n ++ 0^n)` under distinct nonce `lowBits n 1`, whose first counter block is
   also `lowBits n 1`, and check whether the first `n`-bit ciphertext block equals the second block
   of reply 1. -/
def unscaledNonceCTRAdversary : OracleDistinguisher :=
  fun n _ => do
    let z2 := List.replicate (2 * n) false
    let m1 := List.replicate n true ++ List.replicate n false
    let q₀ := frame z2 ++ frame z2 ++ BitString.lowBits n 0
    let q₁ := frame z2 ++ frame m1 ++ BitString.lowBits n 1
    let r₁ ← List.take (2 * n + 1) <$> ProbOracleComp.query ((), q₀)
    let r₂ ← List.take (2 * n + 1) <$> ProbOracleComp.query ((), q₁)
    return ((r₂.drop 1).take n == (r₁.drop 1).drop n)

/-- `unscaledNonceCTRAdversary` is uniform strict oracle PPT (`IsOraclePPT encBool`). -/
theorem isOraclePPT_unscaledNonceCTRAdversary :
    IsOraclePPT encBool unscaledNonceCTRAdversary := by
  ppt [unscaledNonceCTRAdversary]

private theorem zipWith_xor_replicate_false :
    ∀ w : List Bool, List.zipWith Bool.xor (List.replicate w.length false) w = w
  | [] => rfl
  | b :: w => by simp [List.replicate_succ, zipWith_xor_replicate_false w]

private theorem zipWith_xor_replicate_true_ne :
    ∀ w : List Bool, w ≠ [] → List.zipWith Bool.xor (List.replicate w.length true) w ≠ w
  | [], h => (h rfl).elim
  | b :: _, _ => by cases b <;> simp [List.replicate_succ]

/-- At every parameter `n ≥ 1`, `unscaledNonceCTRAdversary` achieves CPA advantage `1` against
`unscaledNonceCTRCipher family n` for any length-preserving `family` on whole-block message
pairs. -/
theorem advantage_cpaExperiment_unscaledNonceCTRAdversary
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} (hn : 1 ≤ n) :
    Game.advantage
      (ProbComp.eval ((unscaledNonceCTRCipher family n).cpaExperiment
        (BitString.sampleList n) (blockPairValid n) (nonceCTRValidNonce id n)
        (NonceCipher.unitCPACodec.adapt (unscaledNonceCTRAdversary n [])) false))
      (ProbComp.eval ((unscaledNonceCTRCipher family n).cpaExperiment
        (BitString.sampleList n) (blockPairValid n) (nonceCTRValidNonce id n)
        (NonceCipher.unitCPACodec.adapt (unscaledNonceCTRAdversary n [])) true)) = 1 := by
  have htwoPow : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hnonceNe : BitString.lowBits n 1 ≠ BitString.lowBits n 0 := fun heq => by
    have hval := congrArg BitString.lsbValue heq
    rw [BitString.lsbValue_lowBits htwoPow,
      BitString.lsbValue_lowBits (Nat.two_pow_pos n)] at hval
    omega
  let z2 := List.replicate (2 * n) false
  let m1 := List.replicate n true ++ List.replicate n false
  have hz2Mod : (2 * n) % n = 0 := Nat.mul_mod_left 2 n
  have hdiv2 : (2 * n + n - 1) / n = 2 := by
    rw [div_ceil_eq_div_of_mod_eq_zero hz2Mod, Nat.mul_div_left 2 (by omega)]
  have hv0 : blockPairValid n z2 z2 = true := by simp [blockPairValid, z2, hz2Mod]
  have hv1 : blockPairValid n z2 m1 = true := by simp [blockPairValid, z2, m1, Nat.two_mul]
  have hvn (j : ℕ) : nonceCTRValidNonce id n (BitString.lowBits n j) = true := by
    simp [nonceCTRValidNonce]
  have heval (b : Bool) :
      ProbComp.eval ((unscaledNonceCTRCipher family n).cpaExperiment
        (BitString.sampleList n) (blockPairValid n) (nonceCTRValidNonce id n)
        (NonceCipher.unitCPACodec.adapt (unscaledNonceCTRAdversary n [])) b) =
      PMF.pure (!b) := by
    rw [NonceCipher.eval_cpaExperiment]
    refine (PMF.bind_congr_on_support _ _ _ fun k hk => ?_).trans (PMF.bind_const _ _)
    rw [BitString.eval_sampleList] at hk
    have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
    rw [NonceCipher.unitCPACodec.runWith_adapt]
    simp only [unscaledNonceCTRAdversary, ProbOracleComp.runWith_bind,
      ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
    let y (j : ℕ) := family k (BitString.lowBits n j)
    have hyLen (j : ℕ) : (y j).length = n := by
      rw [hlen k _ (by rw [BitString.length_lowBits, hkLen]), hkLen]
    have hks (j : ℕ) (hj : j < 2 ^ n) :
        ctrWordKeystream family n k (BitString.lowBits n j) 2 = y j ++ y (j + 1) := by
      simp [ctrWordKeystream, List.range_succ, ctrWordCounter, BitString.lsbValue_lowBits hj, y]
    have hct_z2 (j : ℕ) (hj : j < 2 ^ n) :
        (unscaledNonceCTRCipher family n).encrypt k z2 () (BitString.lowBits n j) =
          y j ++ y (j + 1) := by
      have hlenKs : (y j ++ y (j + 1)).length = 2 * n := by simp [hyLen, Nat.two_mul]
      rw [unscaledNonceCTRCipher, nonceStreamCipher_encrypt_eq]
      simp only [z2, List.length_replicate, hdiv2, hks j hj]
      rw [xorWithStream_eq_zipWith (by simp [hlenKs]), ← hlenKs]
      exact zipWith_xor_replicate_false _
    have hwordCall (m₀ m₁ nonce : List Bool) (seen : List (List Bool))
        (hv : blockPairValid n m₀ m₁ = true) (hvn' : nonceCTRValidNonce id n nonce = true)
        (hfresh : nonce ∉ seen) :
        NonceCipher.unitCPACodec.wordOracle (m := StateT (Bool × List (List Bool)) PMF)
          (fun q state => ProbComp.eval ((unscaledNonceCTRCipher family n).cpaOracle
            (blockPairValid n) (nonceCTRValidNonce id n) k b q state))
          ((), frame m₀ ++ frame m₁ ++ nonce) (true, seen) =
          PMF.pure (true :: (unscaledNonceCTRCipher family n).encrypt k
            ((MessagePair.mk m₀ m₁).select b) () nonce, (true, nonce :: seen)) := by
      rw [show ((), frame m₀ ++ frame m₁ ++ nonce) =
          NonceCipher.unitCPACodec.encodeQuery (⟨m₀, m₁⟩, (), nonce) from rfl,
        NonceCipher.unitCPACodec.wordOracle_encodeQuery]
      dsimp only [Functor.map, StateT.map]
      simp [NonceCipher.cpaOracle, NonceCipher.unitCPACodec, hv, hvn', hfresh, ProbComp.eval_pure]
    have hsel0 : (MessagePair.mk z2 z2).select b = z2 := by cases b <;> rfl
    rw [hwordCall z2 z2 (BitString.lowBits n 0) [] hv0 (hvn 0) (by simp), hsel0,
      hct_z2 0 (Nat.two_pow_pos n)]
    simp only [PMF.pure_map, PMF.pure_bind, Prod.map, id_eq]
    rw [hwordCall z2 m1 (BitString.lowBits n 1) [BitString.lowBits n 0] hv1 (hvn 1)
      (by simp [hnonceNe])]
    simp only [PMF.pure_map, PMF.pure_bind, Prod.map, id_eq]
    have hrTake (ct : List Bool) (hct : ct.length = 2 * n) :
        (true :: ct).take (2 * n + 1) = true :: ct :=
      List.take_of_length_le (by rw [List.length_cons, hct])
    rw [hrTake (y 0 ++ y 1) (by simp [hyLen, Nat.two_mul]), List.drop_succ_cons, List.drop_zero,
      List.drop_left' (hyLen 0)]
    cases b
    · dsimp only [MessagePair.select, cond]
      rw [hct_z2 1 htwoPow, hrTake (y 1 ++ y 2) (by simp [hyLen, Nat.two_mul]),
        List.drop_succ_cons, List.drop_zero, List.take_left' (hyLen 1)]
      simp
    · have hct1True :
          (unscaledNonceCTRCipher family n).encrypt k m1 () (BitString.lowBits n 1) =
            List.zipWith Bool.xor (List.replicate n true) (y 1) ++ y 2 := by
        have hm1Len : m1.length = 2 * n := by simp [m1, Nat.two_mul]
        rw [unscaledNonceCTRCipher, nonceStreamCipher_encrypt_eq, hm1Len, hdiv2, hks 1 htwoPow,
          xorWithStream_eq_zipWith (by simp [m1, hyLen])]
        dsimp only [m1]
        rw [List.zipWith_append (by simp [hyLen]), ← hyLen 2, zipWith_xor_replicate_false]
      have hxorLen : (List.zipWith Bool.xor (List.replicate n true) (y 1)).length = n := by
        simp [hyLen]
      have hneBlock : List.zipWith Bool.xor (List.replicate n true) (y 1) ≠ y 1 :=
        hyLen 1 ▸ zipWith_xor_replicate_true_ne (y 1)
          (List.ne_nil_of_length_pos ((hyLen 1).symm ▸ hn))
      dsimp only [MessagePair.select, cond]
      rw [hct1True, hrTake _ (by simp [hxorLen, hyLen, Nat.two_mul]), List.drop_succ_cons,
        List.drop_zero, List.take_left' hxorLen, beq_eq_false_iff_ne.mpr hneBlock]
      simp
  rw [heval false, heval true, Game.advantage]
  simp [Game.succProbability]

/-- **Unscaled nonce-based counter mode is not CPA-secure** ([BonehShoup2023], Section 5.5.2,
printed p. 203): for every length-preserving family `family`, using `n`-bit nonces directly as
initial counters without scaling fails `NonceCipher.INDCPA` on whole-block message pairs (with no
block cap; `unscaledNonceCTRAdversary` uses 2-block queries). -/
theorem not_indcpa_unscaledNonceCTRCipher {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length) :
    ¬ NonceCipher.INDCPA (fun n => unscaledNonceCTRCipher family n)
        BitString.sampleList blockPairValid (nonceCTRValidNonce id) := by
  intro hcpa
  exact not_negligible_const one_ne_zero
    (((hcpa unscaledNonceCTRAdversary isOraclePPT_unscaledNonceCTRAdversary).shift 1).congr fun n =>
      advantage_cpaExperiment_unscaledNonceCTRAdversary hlen (Nat.succ_pos n))

end Cslib.Crypto
