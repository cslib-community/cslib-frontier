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
  conv_lhs => rw [xorWithStream]
  rw [length_xorWithStream]
  unfold xorWithStream
  refine BitString.zipWith_xor_self_right msg _ ?_
  simp only [List.length_append, List.length_take, List.length_replicate]
  omega

private theorem xorWithStream_eq_zipWith {msg stream : List Bool} (h : stream.length = msg.length) :
    xorWithStream msg stream = List.zipWith Bool.xor msg stream := by
  rw [xorWithStream, List.take_of_length_le h.le, h, Nat.sub_self, List.replicate_zero,
    List.append_nil]

private theorem div_ceil_eq_div_of_mod_eq_zero {m n : ℕ} (h : m % n = 0) :
    (m + n - 1) / n = m / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
    have heq : n * q + n - 1 = (n - 1) + n * q := by omega
    rw [heq, Nat.add_mul_div_left _ _ hn, Nat.mul_div_right _ hn,
      Nat.div_eq_zero_iff.mpr (Or.inr (by omega)), zero_add]

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
  have heq : (fun a => nonceCTRValid nonceLen (n a) (m₀ a) (m₁ a)) =
      fun a => blockPairValid (n a) (m₀ a) (m₁ a) &&
        decide (Nat.clog 2 ((m₀ a).length / n a) ≤ n a - nonceLen (n a)) := by
    funext a
    simp only [nonceCTRValid, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  rw [heq]
  have hclog : ComputableInPolyTime (fun a => Nat.clog 2 ((m₀ a).length / n a)) input encUnary :=
    (ComputableInPolyTime.unary_clog_const 2).comp (by polytime)
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
        dropFrame (dropFrame word) == word) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have hsome : NonceCipher.unitCPACodec.decodeQuery ((), word) =
          some (⟨unframe word, unframe (dropFrame word)⟩, (), dropFrame (dropFrame word)) := by
        rw [NonceCipher.unitCPACodec.decodeQuery_eq_some_iff]
        exact Prod.ext rfl heq
      rw [hdec] at hsome
      cases hsome
    rw [hfalse]
    rfl
  | some q =>
    rcases q with ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
    have henc := (NonceCipher.unitCPACodec.decodeQuery_eq_some_iff ((), word)
      (⟨m₀, m₁⟩, (), nonce)).mp hdec
    have hword : frame m₀ ++ (frame m₁ ++ nonce) = word := by
      simpa [NonceCipher.unitCPACodec, List.append_assoc] using congrArg Prod.snd henc
    have hm₀ : unframe word = m₀ := by rw [← hword, unframe_frame_append]
    have hrest : dropFrame word = frame m₁ ++ nonce := by rw [← hword, dropFrame_frame_append]
    have hm₁ : unframe (dropFrame word) = m₁ := by rw [hrest, unframe_frame_append]
    have hnonce : dropFrame (dropFrame word) = nonce := by rw [hrest, dropFrame_frame_append]
    have htrue : (frame m₀ ++ frame m₁ ++ nonce == word) = true := by
      rw [beq_iff_eq, List.append_assoc]
      exact hword
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
  have hunframe : ComputableInPolyTime unframe encBits encBits :=
    ComputableInPolyTime.unframe
  have hdrop : ComputableInPolyTime dropFrame encBits encBits :=
    ComputableInPolyTime.dropFrame
  have hnCall : ComputableInPolyTime (fun x : HandlerCall => x.1.1.1)
      encHandlerCallNonceCTR encUnary := by fun_prop
  have hbCall : ComputableInPolyTime (fun x : HandlerCall => x.1.2)
      encHandlerCallNonceCTR encBool := by fun_prop
  have hword : ComputableInPolyTime (fun x : HandlerCall => x.2.1.2)
      encHandlerCallNonceCTR encBits := by fun_prop
  have hok : ComputableInPolyTime (fun x : HandlerCall => x.2.2.1)
      encHandlerCallNonceCTR encBool := by fun_prop
  have hseen : ComputableInPolyTime (fun x : HandlerCall => x.2.2.2)
      encHandlerCallNonceCTR (encList encBits) := by fun_prop
  have hm₀ : ComputableInPolyTime (fun x : HandlerCall => unframe x.2.1.2)
      encHandlerCallNonceCTR encBits := hunframe.comp hword
  have hrest : ComputableInPolyTime (fun x : HandlerCall => dropFrame x.2.1.2)
      encHandlerCallNonceCTR encBits := hdrop.comp hword
  have hm₁ : ComputableInPolyTime (fun x : HandlerCall => unframe (dropFrame x.2.1.2))
      encHandlerCallNonceCTR encBits := hunframe.comp hrest
  have hnonce : ComputableInPolyTime (fun x : HandlerCall => dropFrame (dropFrame x.2.1.2))
      encHandlerCallNonceCTR encBits := hdrop.comp hrest
  have hsCall : ComputableInPolyTime (fun x : HandlerCall => nonceLen x.1.1.1)
      encHandlerCallNonceCTR encUnary := hnonceLen.comp hnCall
  have hvalid : ComputableInPolyTime
      (fun x : HandlerCall =>
        nonceCTRValid nonceLen x.1.1.1 (unframe x.2.1.2) (unframe (dropFrame x.2.1.2)))
      encHandlerCallNonceCTR encBool :=
    computableInPolyTime_nonceCTRValid hnonceLen hnCall hm₀ hm₁
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
      have hraw := ComputableInPolyTime.encoding_comp (hm₀.prod (hm₁.prod hnonce))
      convert hraw using 1
      funext x
      simp [encPair_apply, List.append_assoc]
    simpa only [beq_eq_decide] using ComputableInPolyTime.decide_eq' henc3 hword
  have hvn : ComputableInPolyTime
      (fun x : HandlerCall => nonceCTRValidNonce nonceLen x.1.1.1 (dropFrame (dropFrame x.2.1.2)))
      encHandlerCallNonceCTR encBool := by
    have hnl : ComputableInPolyTime (fun x : HandlerCall => (dropFrame (dropFrame x.2.1.2)).length)
        encHandlerCallNonceCTR encUnary := ComputableInPolyTime.length_bits.comp hnonce
    simpa only [nonceCTRValidNonce, beq_eq_decide] using
      ComputableInPolyTime.decide_eq' hnl hsCall
  have hfresh : ComputableInPolyTime
      (fun x : HandlerCall => decide (dropFrame (dropFrame x.2.1.2) ∉ x.2.2.2))
      encHandlerCallNonceCTR encBool :=
    ComputableInPolyTime.decide_not (ComputableInPolyTime.decide_mem hseen hnonce)
  have hcondInner : ComputableInPolyTime
      (fun x : HandlerCall =>
        x.2.2.1 &&
          nonceCTRValid nonceLen x.1.1.1 (unframe x.2.1.2) (unframe (dropFrame x.2.1.2)) &&
          nonceCTRValidNonce nonceLen x.1.1.1 (dropFrame (dropFrame x.2.1.2)) &&
          decide (dropFrame (dropFrame x.2.1.2) ∉ x.2.2.2))
      encHandlerCallNonceCTR encBool :=
    ComputableInPolyTime.bool_and'
      (ComputableInPolyTime.bool_and' (ComputableInPolyTime.bool_and' hok hvalid) hvn) hfresh
  have hblocks : ComputableInPolyTime
      (fun x : HandlerCall => (unframe x.2.1.2).length / x.1.1.1)
      encHandlerCallNonceCTR encUnary :=
    ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hm₀) hnCall
  have hks : IsOraclePPTOn encHandlerCallNonceCTR encBits
      (fun x : HandlerCall =>
        ctrKeystreamQueries x.1.1.1
          (nonceCTRCounter x.1.1.1 (nonceLen x.1.1.1) (dropFrame (dropFrame x.2.1.2)) 0)
          ((unframe x.2.1.2).length / x.1.1.1)) :=
    isOraclePPTOn_ctrKeystreamQueries hnCall
      (computableInPolyTime_nonceCTRCounter_zero hnCall hsCall hnonce) hblocks
  have hyesInner : IsOraclePPTOn encHandlerCallNonceCTR
      (encPair encBits (encPair encBool (encList encBits)))
      (fun x : HandlerCall =>
        (fun stream =>
          (true :: xorWithStream
            ((MessagePair.mk (unframe x.2.1.2) (unframe (dropFrame x.2.1.2))).select x.1.2)
            stream,
            (true, dropFrame (dropFrame x.2.1.2) :: x.2.2.2))) <$>
          ctrKeystreamQueries x.1.1.1
            (nonceCTRCounter x.1.1.1 (nonceLen x.1.1.1) (dropFrame (dropFrame x.2.1.2)) 0)
            ((unframe x.2.1.2).length / x.1.1.1)) := by
    refine hks.map_with ?_
    let fstP := ComputableInPolyTime.fst encHandlerCallNonceCTR encBits
    let sndP := ComputableInPolyTime.snd encHandlerCallNonceCTR encBits
    have hsel : ComputableInPolyTime
        (fun p : HandlerCall × List Bool =>
          if p.1.1.2 then unframe (dropFrame p.1.2.1.2) else unframe p.1.2.1.2)
        (encPair encHandlerCallNonceCTR encBits) encBits := by
      have hbP := hbCall.comp fstP
      have hm₁P := hm₁.comp fstP
      have hm₀P := hm₀.comp fstP
      polytime
    have hselEq (p : HandlerCall × List Bool) :
        (MessagePair.mk (unframe p.1.2.1.2) (unframe (dropFrame p.1.2.1.2))).select p.1.1.2 =
          if p.1.1.2 then unframe (dropFrame p.1.2.1.2) else unframe p.1.2.1.2 := by
      cases p.1.1.2 <;> rfl
    have hxor : ComputableInPolyTime
        (fun p : HandlerCall × List Bool =>
          true :: xorWithStream
            ((MessagePair.mk (unframe p.1.2.1.2) (unframe (dropFrame p.1.2.1.2))).select p.1.1.2)
            p.2)
        (encPair encHandlerCallNonceCTR encBits) encBits := by
      have heqXor : (fun p : HandlerCall × List Bool =>
            true :: xorWithStream
              ((MessagePair.mk (unframe p.1.2.1.2) (unframe (dropFrame p.1.2.1.2))).select p.1.1.2)
              p.2) =
          fun p => true :: xorWithStream
            (if p.1.1.2 then unframe (dropFrame p.1.2.1.2) else unframe p.1.2.1.2) p.2 := by
        funext p
        rw [hselEq p]
      rw [heqXor]
      exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
        (computableInPolyTime_xorWithStream hsel sndP)
    exact hxor.prod ((ComputableInPolyTime.const true).prod
      (ComputableInPolyTime.cons' (hnonce.comp fstP) (hseen.comp fstP)))
  have hnoInner : IsOraclePPTOn (Operation := Unit) encHandlerCallNonceCTR
      (encPair encBits (encPair encBool (encList encBits)))
      (fun x : HandlerCall => pure ([], (false, x.2.2.2))) := by
    ppt
  have hnoOuter : IsOraclePPTOn (Operation := Unit) encHandlerCallNonceCTR
      (encPair encBits (encPair encBool (encList encBits)))
      (fun x : HandlerCall => pure ([], x.2.2)) := by
    have hst : ComputableInPolyTime (fun x : HandlerCall => x.2.2)
        encHandlerCallNonceCTR (encPair encBool (encList encBits)) := hok.prod hseen
    ppt
  have heq : (fun x : HandlerCall => nonceCTRHandler nonceLen x.1.1.1 x.1.2 x.2.1 x.2.2) =
      fun x =>
        if frame (unframe x.2.1.2) ++ frame (unframe (dropFrame x.2.1.2)) ++
            dropFrame (dropFrame x.2.1.2) == x.2.1.2 then
          if x.2.2.1 &&
              nonceCTRValid nonceLen x.1.1.1 (unframe x.2.1.2) (unframe (dropFrame x.2.1.2)) &&
              nonceCTRValidNonce nonceLen x.1.1.1 (dropFrame (dropFrame x.2.1.2)) &&
              decide (dropFrame (dropFrame x.2.1.2) ∉ x.2.2.2) then
            (fun stream =>
              (true :: xorWithStream
                ((MessagePair.mk (unframe x.2.1.2) (unframe (dropFrame x.2.1.2))).select x.1.2)
                stream,
                (true, dropFrame (dropFrame x.2.1.2) :: x.2.2.2))) <$>
              ctrKeystreamQueries x.1.1.1
                (nonceCTRCounter x.1.1.1 (nonceLen x.1.1.1) (dropFrame (dropFrame x.2.1.2)) 0)
                ((unframe x.2.1.2).length / x.1.1.1)
          else
            pure ([], (false, x.2.2.2))
        else
          pure ([], x.2.2) :=
    funext fun x => nonceCTRHandler_eq_ite nonceLen x.1.1.1 x.1.2 x.2.1 x.2.2
  rw [heq]
  exact IsOraclePPTOn.cond hcondOuter (IsOraclePPTOn.cond hcondInner hyesInner hnoInner)
    hnoOuter

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
    intro cb request state _ result hresult
    rcases state with ⟨ok, seen⟩
    unfold nonceCTRHandler at hresult
    cases hdec : NonceCipher.unitCPACodec.decodeQuery request with
    | none =>
      simp only [hdec] at hresult
      rw [OracleComp.eq_of_mem_supportWith_pure hresult]
      exact ⟨trivial, by simp, by dsimp only; omega⟩
    | some q =>
      rcases q with ⟨⟨m₀, m₁⟩, ⟨⟩, nonce⟩
      simp only [hdec] at hresult
      have hword : frame m₀ ++ frame m₁ ++ nonce = request.2 :=
        congrArg Prod.snd ((NonceCipher.unitCPACodec.decodeQuery_eq_some_iff request _).mp hdec)
      have hlen : 2 * m₀.length + 2 * m₁.length + nonce.length + 2 = request.2.length := by
        rw [← hword]
        simp only [List.length_append, length_frame]
        omega
      split_ifs at hresult with hcond
      · obtain ⟨stream, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
        have hselLen : ((MessagePair.mk m₀ m₁).select cb.2).length ≤ m₀.length + m₁.length := by
          cases cb.2 <;> simp [MessagePair.select]
        refine ⟨trivial, ?_, ?_⟩
        · simp only [List.length_cons, length_xorWithStream]
          omega
        · simp only [length_encPair, encBool_apply, List.length_singleton, encList_cons,
            encBits_apply, List.length_append, length_frame]
          omega
      · rw [OracleComp.eq_of_mem_supportWith_pure hresult]
        refine ⟨trivial, by simp, ?_⟩
        dsimp only
        simp only [length_encPair, encBool_apply, List.length_singleton]
        omega
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
  simp only [prfRealGame, id_eq, nonceCTRSimView, ProbOracleComp.run_bind, ProbOracleComp.run_pure,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  rw [BitString.eval_sampleList] at hk
  have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
  rw [NonceCipher.unitCPACodec.runWith_adapt]
  have hread := ProbOracleComp.runWith_readOnly
    (fun request (_ : Unit) => PMF.pure (prfOracle family n k request.2))
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (nonceCTRHandler nonceLen n b))
      (adversary n [])).run (true, [])) ()
  have hfst := congrArg (PMF.map Prod.fst) hread
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show (fun x : Bool × Bool × List (List Bool) => x) = id from rfl, PMF.map_id] at hfst
  rw [ProbOracleComp.eval_run, ← OracleComp.evalWith_eq_interpret]
  simp only [ProbComp.eval_pure]
  rw [← hfst, ProbOracleComp.runWith_run_interpret]
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q (state : (Bool × List (List Bool)) × Unit) =>
      (ProbOracleComp.runWith
        (fun request (u : Unit) => (PMF.pure (prfOracle family n k request.2)).map (·, u))
        ((nonceCTRHandler nonceLen n b q).run state.1) state.2).map
          (fun ⟨⟨a, s'⟩, u⟩ => (a, s', u)))
    (oracle' := NonceCipher.unitCPACodec.wordOracle (m := StateT (Bool × List (List Bool)) PMF)
      (fun q state => ProbComp.eval
        ((nonceCTRCipher family n (nonceLen n)).cpaOracle
          (nonceCTRValid nonceLen n) (nonceCTRValidNonce nonceLen n) k b q state)))
    (represent := Prod.fst)
    (step := by
      intro request ⟨⟨ok, seen⟩, ⟨⟩⟩
      have hunit (prog : WordOracleComp Unit (List Bool × (Bool × List (List Bool)))) :
          (ProbOracleComp.runWith
            (fun req (u : Unit) => (PMF.pure (prfOracle family n k req.2)).map (·, u))
            prog ()).map (fun ⟨⟨a, s'⟩, _⟩ => (a, s')) =
          ProbComp.eval (prog.run fun req => pure (prfOracle family n k req.2)) := by
        have hr := ProbOracleComp.runWith_readOnly
          (fun req (_ : Unit) => PMF.pure (prfOracle family n k req.2)) prog ()
        have hf := congrArg (PMF.map fun ⟨⟨a, s'⟩, _⟩ => (a, s')) hr
        simp only [PMF.map_comp, Function.comp_def] at hf
        rw [show (fun x : List Bool × (Bool × List (List Bool)) => (x.1, x.2)) = id from rfl,
          PMF.map_id] at hf
        rw [hf, ProbOracleComp.eval_run, ← OracleComp.evalWith_eq_interpret]
        simp only [ProbComp.eval_pure]
      simp only [PMF.map_comp, Function.comp_def]
      change (ProbOracleComp.runWith
          (fun req (u : Unit) => (PMF.pure (prfOracle family n k req.2)).map (·, u))
          ((nonceCTRHandler nonceLen n b request).run (ok, seen)) ()).map
            (fun ⟨⟨a, s'⟩, _⟩ => (a, s')) = _
      rw [hunit]
      unfold nonceCTRHandler OracleCodec.wordOracle NonceCipher.cpaOracle
      cases hdec : NonceCipher.unitCPACodec.decodeQuery request with
      | none =>
        dsimp only [StateT.run]
        rw [ProbOracleComp.run_pure, ProbComp.eval_pure]
        rfl
      | some q =>
        rcases q with ⟨pair, ⟨⟩, nonce⟩
        dsimp only [StateT.run]
        split_ifs with hcond
        · have hcond' := hcond
          simp only [Bool.and_eq_true, nonceCTRValid, blockPairValid, nonceCTRValidNonce,
            beq_iff_eq] at hcond
          rcases hcond with ⟨⟨⟨_, ⟨hlenPair, hmod⟩, _⟩, _⟩, _⟩
          have hselMod : (pair.select b).length % n = 0 := by
            cases b <;> simp [MessagePair.select, ← hlenPair, hmod]
          have hselDiv : ((pair.select b).length + n - 1) / n = pair.msg₀.length / n := by
            rw [div_ceil_eq_div_of_mod_eq_zero hselMod]
            cases b <;> simp [MessagePair.select, hlenPair]
          rw [ProbOracleComp.run_map, run_ctrKeystreamQueries hlen hkLen,
            map_pure, ProbComp.eval_pure]
          dsimp only [Functor.map, StateT.map]
          split_ifs with hcond2
          · rw [ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.monad_pure_eq_pure,
              nonceCTRCipher, nonceStreamCipher_encrypt_eq, hselDiv]
            rfl
          · exfalso
            apply hcond2
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond'
        · rw [ProbOracleComp.run_pure, ProbComp.eval_pure]
          dsimp only [Functor.map, StateT.map]
          split_ifs with hcond2
          · exfalso
            apply hcond
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond2
          · rw [ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.pure_bind, PMF.monad_pure_eq_pure]
            rfl)
    (adversary n []) ((true, []), ())
  have hbind_eq_map {α β : Type} (p : PMF α) (f : α → β) :
      (p.bind fun a => PMF.pure (f a)) = p.map f := rfl
  rw [hbind_eq_map]
  have hmap := congrArg (PMF.map fun (guess, ok, _) => ok && guess) hsim
  simpa only [PMF.map_comp, Function.comp_def] using hmap

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
      refine ⟨?_, by simp⟩
      intro res hres
      rw [PMF.mem_support_pure_iff] at hres
      subst hres
      exact ⟨rfl, by simp, fun x hx => Or.inl (hcache x hx)⟩
    | succ k ih =>
      obtain ⟨hsupp, hlaw⟩ := ih (Nat.le_of_succ_le hk)
      have hkPow : k < 2 ^ (n - s) := lt_of_lt_of_le (Nat.lt_succ_self k) (hk.trans hblocks)
      let qk := nonceCTRCounter n s nonce k
      have hqkLen : qk.length = n := length_nonceCTRCounter hs hnonce k
      let xk := BitString.ofList n qk
      have hxkOfFn : List.ofFn xk = qk := BitString.ofFn_ofList hqkLen
      have hxkDrop : (List.ofFn xk).drop (n - s) = nonce := by
        rw [hxkOfFn]
        dsimp only [qk, nonceCTRCounter]
        exact List.drop_left' (BitString.length_lowBits (n - s) k)
      have hxkTake : BitString.lsbValue ((List.ofFn xk).take (n - s)) = k := by
        rw [hxkOfFn]
        dsimp only [qk, nonceCTRCounter]
        rw [List.take_left' (BitString.length_lowBits (n - s) k), BitString.lsbValue_lowBits hkPow]
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
          · rw [hxkTake] at hlt
            exact Nat.lt_irrefl k hlt
        rcases mid with ⟨⟨idx, stream⟩, cacheMid⟩
        dsimp only at hidx hnone ⊢
        subst idx
        simp only [ctrKeystreamStep, iv, ctrWordCounter_nonceCTRCounter_zero hs hnonce hkPow,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
        have hlro : lazyRandomFunctionOracle n n (nonceCTRCounter n s nonce k) cacheMid =
            (PMF.uniformOfFintype (BitString n)).map fun y =>
              (List.ofFn y, Function.update cacheMid xk (some y)) :=
          lazyRandomFunctionOracle_of_none hqkLen hnone
        rw [hlro, PMF.map_comp, PMF.map_comp]
        refine congrArg (fun f => (PMF.uniformOfFintype (BitString n)).map f) (funext fun y => ?_)
        simp [Prod.map, List.take_of_length_le (List.length_ofFn (f := y)).le]
      dsimp only
      rw [OracleComp.iterate_succ, ProbOracleComp.runWith_bind]
      refine ⟨?_, ?_⟩
      · intro res hres
        rw [PMF.mem_support_bind_iff] at hres
        obtain ⟨mid, hmid, hresMid⟩ := hres
        rw [hstep_of_supp mid hmid, PMF.mem_support_map_iff] at hresMid
        obtain ⟨y, -, rfl⟩ := hresMid
        obtain ⟨_, hstreamLen, hmidCache⟩ := hsupp mid hmid
        refine ⟨rfl, by simp [hstreamLen, Nat.succ_mul], fun x hx => ?_⟩
        dsimp only at hx
        by_cases hxx : x = xk
        · subst hxx
          exact Or.inr ⟨hxkDrop, by rw [hxkTake]; exact Nat.lt_succ_self k⟩
        · rw [Function.update_of_ne hxx] at hx
          rcases hmidCache x hx with hmem | ⟨hd, hlt⟩
          · exact Or.inl hmem
          · exact Or.inr ⟨hd, Nat.lt_succ_of_lt hlt⟩
      · rw [PMF.map_bind]
        have hcongr : (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
            (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache).bind
              (fun mid => (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
                (ctrKeystreamStep n iv mid.1) mid.2).map (fun res => res.1.2)) =
            (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
              (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache).bind
              (fun mid => (BitString.uniformList n).map (mid.1.2 ++ ·)) := by
          refine PMF.bind_congr_on_support _ _ _ fun mid hmid => ?_
          rw [hstep_of_supp mid hmid]
          simp [BitString.uniformList, PMF.map_comp, Function.comp_def]
        have hfactor :
            ((ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
              (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache).map
                (fun mid : (ℕ × List Bool) × _ => mid.1.2)).bind
                  (fun stream => (BitString.uniformList n).map (stream ++ ·)) =
            (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
              (OracleComp.iterate k (ctrKeystreamStep n iv) (0, [])) cache).bind
                (fun mid => (BitString.uniformList n).map (mid.1.2 ++ ·)) :=
          PMF.bind_map _ (fun mid : (ℕ × List Bool) × _ => mid.1.2)
            (fun stream => (BitString.uniformList n).map (stream ++ ·))
        rw [hcongr, ← hfactor, hlaw, ← BitString.uniformList_add, Nat.succ_mul]
  obtain ⟨hsupp, hlaw⟩ := hloop blocks le_rfl
  dsimp only [ctrKeystreamQueries, iv]
  rw [ProbOracleComp.runWith_map]
  refine ⟨?_, ?_⟩
  · intro res hres
    rw [PMF.mem_support_map_iff] at hres
    obtain ⟨mid, hmid, rfl⟩ := hres
    intro x hx
    rcases (hsupp mid hmid).2.2 x hx with hmem | ⟨hd, -⟩
    · exact List.mem_cons_of_mem _ hmem
    · rw [hd]
      exact List.mem_cons_self
  · simpa only [PMF.map_comp, Function.comp_def, Prod.map] using hlaw

private theorem eval_prfIdealGame_nonceCTRSimView {nonceLen : ℕ → ℕ} {n : ℕ} (hs : nonceLen n ≤ n)
    (adversary : OracleDistinguisher) (b : Bool) :
    ProbComp.eval (prfIdealGame id id (nonceCTRSimView nonceLen adversary b) n) =
      (ProbOracleComp.runWith (nonceCTRIdealOracle nonceLen n) (adversary n []) (true, [])).map
        fun (guess, ok, _) => ok && guess := by
  classical
  rw [prfIdealGame_eq_lazy]
  simp only [id_eq]
  rw [← ProbOracleComp.runWith_eq_run_interpret]
  simp only [nonceCTRSimView, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure,
    PMF.map_bind, PMF.pure_map]
  rw [ProbOracleComp.runWith_run_interpret]
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
      rw [ProbOracleComp.runWith_pure]
      refine ⟨?_, by simp [PMF.pure_map]⟩
      intro a state' hmem
      simp only [PMF.pure_map, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      exact hinv
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
        refine ⟨?_, ?_⟩
        · intro a state' hmem
          rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨ksRes, hksRes, heq⟩ := hmem
          cases heq
          exact hsuppKs ksRes hksRes
        · have hmapXor :
              (ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
                (ctrKeystreamQueries n (nonceCTRCounter n (nonceLen n) nonce 0)
                  (pair.msg₀.length / n)) cache).map
                  (fun ksRes =>
                    (true :: xorWithStream (pair.select b) ksRes.1, (true, nonce :: seen))) =
              ((ProbOracleComp.runWith (fun req => lazyRandomFunctionOracle n n req.2)
                (ctrKeystreamQueries n (nonceCTRCounter n (nonceLen n) nonce 0)
                  (pair.msg₀.length / n)) cache).map
                  Prod.fst).map
                (fun stream =>
                  (true :: xorWithStream (pair.select b) stream, (true, nonce :: seen))) := by
            simp [PMF.map_comp, Function.comp_def]
          have hxorUnif :
              (BitString.uniformList pair.msg₀.length).map
                (fun stream =>
                  (true :: xorWithStream (pair.select b) stream, (true, nonce :: seen))) =
              (BitString.uniformList pair.msg₀.length).map
                (fun ct => (true :: ct, (true, nonce :: seen))) := by
            conv_rhs => rw [← hselLen, ← uniformList_map_xorWithStream (pair.select b)]
            simp [PMF.map_comp, Function.comp_def, hselLen]
          rw [hmapXor, hlawKs, hmulBlocks, hxorUnif]
      · rw [ProbOracleComp.runWith_pure]
        refine ⟨?_, by simp [PMF.pure_map]⟩
        intro a state' hmem
        simp only [PMF.pure_map, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩
        exact hinv
  have hsim := ProbOracleComp.runWith_map_state_of_invariant
    jointOracle (nonceCTRIdealOracle nonceLen n) Prod.fst inv
    (fun q s hs a s' hmem => (hstep_inv_and_law q s hs).1 a s' hmem)
    (fun q s hs => (hstep_inv_and_law q s hs).2)
    (adversary n []) ((true, []), fun _ => none) (fun _ hx => (hx rfl).elim)
  have hbind_eq_map {α β : Type} (p : PMF α) (f : α → β) :
      (p.bind fun a => PMF.pure (f a)) = p.map f := rfl
  rw [hbind_eq_map]
  have hmap := congrArg (PMF.map fun (guess, ok, _) => ok && guess) hsim
  simpa only [PMF.map_comp, Function.comp_def, jointOracle] using hmap

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
  simp only [nonceCTRToPRF, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbOracleComp.run_map, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_map]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind (PMF.uniformOfFintype Bool)) (funext fun b => ?_)
  rw [PMF.map_bind]

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
    unfold prfRealGame
    rw [eval_prfGame_nonceCTRToPRF_eq_bind]
    refine congrArg (PMF.bind (PMF.uniformOfFintype Bool)) (funext fun b => ?_)
    rw [← eval_prfRealGame_nonceCTRSimView hlen adversary b]
    rfl
  have hideal : ProbComp.eval (prfIdealGame id id (nonceCTRToPRF nonceLen adversary) n) =
      PMF.uniformOfFintype Bool := by
    unfold prfIdealGame
    rw [eval_prfGame_nonceCTRToPRF_eq_bind]
    have hconst : (fun b : Bool =>
        (ProbComp.eval (prfIdealGame id id (nonceCTRSimView nonceLen adversary b) n)).map
          (· == b)) =
        fun b => ((ProbOracleComp.runWith (nonceCTRIdealOracle nonceLen n)
          (adversary n []) (true, [])).map fun (guess, ok, _) => ok && guess).map (· == b) := by
      funext b
      rw [eval_prfIdealGame_nonceCTRSimView hs adversary b]
    change ((PMF.uniformOfFintype Bool).bind fun b =>
      (ProbComp.eval (prfIdealGame id id (nonceCTRSimView nonceLen adversary b) n)).map
        (· == b)) = _
    rw [hconst]
    exact Game.uniform_bool_bind_map_beq_const _
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
  let input := encPair encUnary encBits
  change IsOraclePPTOn input encBool (fun a : ℕ × List Bool =>
    unscaledNonceCTRAdversary a.1 a.2)
  have hp := ComputableInPolyTime.id' (encIn := input)
  have hn := hp.fst'
  have htwo := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hn
  have hz := (ComputableInPolyTime.bitsReplicate false).comp htwo
  have hm := ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate true).comp hn)
    ((ComputableInPolyTime.bitsReplicate false).comp hn)
  have hframe := ComputableInPolyTime.bitsFrame encBits
  have hq₀ := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (hframe.comp hz) (hframe.comp hz))
    (ComputableInPolyTime.bitsLow hn (ComputableInPolyTime.const 0))
  have hq₁ := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (hframe.comp hz) (hframe.comp hm))
    (ComputableInPolyTime.bitsLow hn (ComputableInPolyTime.const 1))
  have hlimit := ComputableInPolyTime.unary_add' htwo (ComputableInPolyTime.const 1)
  have hfirst := IsOraclePPTOn.query_take () hq₀ hlimit
  have hprepare := ComputableInPolyTime.fst input encBits
  have hsecond := IsOraclePPTOn.query_take () (hq₁.comp hprepare) (hlimit.comp hprepare)
  have hr := ComputableInPolyTime.id' (encIn := encPair (encPair input encBits) encBits)
  have hleft := (hr.snd'.bitsDropWithInput (ComputableInPolyTime.const 1)).bitsTakeWithInput
    hr.fst'.fst'.fst'
  have hright := (hr.fst'.snd'.bitsDropWithInput
    (ComputableInPolyTime.const 1)).bitsDropWithInput hr.fst'.fst'.fst'
  simpa only [unscaledNonceCTRAdversary, Function.comp_def, bind_pure_comp, encBits_apply] using
    hfirst.bind_with (hsecond.map_with (hleft.beq hright))

private theorem zipWith_xor_replicate_false :
    ∀ w : List Bool, List.zipWith Bool.xor (List.replicate w.length false) w = w
  | [] => rfl
  | b :: w => by simp [List.replicate_succ, zipWith_xor_replicate_false w]

private theorem zipWith_xor_replicate_true_ne :
    ∀ w : List Bool, w ≠ [] → List.zipWith Bool.xor (List.replicate w.length true) w ≠ w
  | [], h => (h rfl).elim
  | b :: w, _ => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
    intro heq
    have hb := (List.cons.inj heq).1
    cases b <;> simp at hb

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
  have hnonceNe : BitString.lowBits n 1 ≠ BitString.lowBits n 0 := by
    intro heq
    have hval := congrArg BitString.lsbValue heq
    rw [BitString.lsbValue_lowBits htwoPow,
      BitString.lsbValue_lowBits (Nat.two_pow_pos n)] at hval
    omega
  let z2 := List.replicate (2 * n) false
  let m1 := List.replicate n true ++ List.replicate n false
  have hz2Mod : (2 * n) % n = 0 := Nat.mul_mod_left 2 n
  have hdiv2 : (2 * n + n - 1) / n = 2 := by
    rw [div_ceil_eq_div_of_mod_eq_zero hz2Mod, Nat.mul_div_left 2 (by omega)]
  have hv0 : blockPairValid n z2 z2 = true := by
    simp [blockPairValid, z2, hz2Mod]
  have hv1 : blockPairValid n z2 m1 = true := by
    simp [blockPairValid, z2, m1, Nat.two_mul]
  have hvn0 : nonceCTRValidNonce id n (BitString.lowBits n 0) = true := by
    simp [nonceCTRValidNonce]
  have hvn1 : nonceCTRValidNonce id n (BitString.lowBits n 1) = true := by
    simp [nonceCTRValidNonce]
  have heval (b : Bool) :
      ProbComp.eval ((unscaledNonceCTRCipher family n).cpaExperiment
        (BitString.sampleList n) (blockPairValid n) (nonceCTRValidNonce id n)
        (NonceCipher.unitCPACodec.adapt (unscaledNonceCTRAdversary n [])) b) =
      PMF.pure (!b) := by
    rw [NonceCipher.eval_cpaExperiment]
    trans (ProbComp.eval (BitString.sampleList n)).bind (fun _ => PMF.pure (!b))
    · refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
      rw [BitString.eval_sampleList] at hk
      have hkLen : k.length = n := BitString.length_of_mem_support_uniformList hk
      rw [NonceCipher.unitCPACodec.runWith_adapt]
      simp only [unscaledNonceCTRAdversary, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure]
      have hyLen (j : ℕ) : (family k (BitString.lowBits n j)).length = n := by
        rw [hlen k _ (by rw [BitString.length_lowBits, hkLen]), hkLen]
      let y₀ := family k (BitString.lowBits n 0)
      let y₁ := family k (BitString.lowBits n 1)
      let y₂ := family k (BitString.lowBits n 2)
      have hks0 : ctrWordKeystream family n k (BitString.lowBits n 0) 2 = y₀ ++ y₁ := by
        simp [ctrWordKeystream, List.range_succ, ctrWordCounter,
          BitString.lsbValue_lowBits (Nat.two_pow_pos n), y₀, y₁]
      have hks1 : ctrWordKeystream family n k (BitString.lowBits n 1) 2 = y₁ ++ y₂ := by
        simp [ctrWordKeystream, List.range_succ, ctrWordCounter,
          BitString.lsbValue_lowBits htwoPow, y₁, y₂]
      have hct0 : (unscaledNonceCTRCipher family n).encrypt k z2 () (BitString.lowBits n 0) =
          y₀ ++ y₁ := by
        have hlenKs0 : (y₀ ++ y₁).length = 2 * n := by
          simp [y₀, y₁, hyLen, Nat.two_mul]
        rw [unscaledNonceCTRCipher, nonceStreamCipher_encrypt_eq]
        simp only [z2, List.length_replicate, hdiv2, hks0]
        rw [xorWithStream_eq_zipWith (by simp [hlenKs0]), ← hlenKs0]
        exact zipWith_xor_replicate_false (y₀ ++ y₁)
      have hsel0 : (MessagePair.mk z2 z2).select b = z2 := by cases b <;> rfl
      have hcall0 : NonceCipher.unitCPACodec.wordOracle
          (m := StateT (Bool × List (List Bool)) PMF)
          (fun q state => ProbComp.eval ((unscaledNonceCTRCipher family n).cpaOracle
            (blockPairValid n) (nonceCTRValidNonce id n) k b q state))
          ((), frame z2 ++ frame z2 ++ BitString.lowBits n 0) (true, []) =
          PMF.pure (true :: (y₀ ++ y₁), (true, [BitString.lowBits n 0])) := by
        rw [show ((), frame z2 ++ frame z2 ++ BitString.lowBits n 0) =
            NonceCipher.unitCPACodec.encodeQuery (⟨z2, z2⟩, (), BitString.lowBits n 0) from rfl,
          NonceCipher.unitCPACodec.wordOracle_encodeQuery]
        change (ProbComp.eval ((unscaledNonceCTRCipher family n).cpaOracle
            (blockPairValid n) (nonceCTRValidNonce id n) k b
            (⟨z2, z2⟩, (), BitString.lowBits n 0) (true, []))).map
            (fun p => (encOption encBits p.1, p.2)) = _
        simp [NonceCipher.cpaOracle, hv0, hvn0, hsel0, hct0, ProbComp.eval_pure]
      have hcall1 : NonceCipher.unitCPACodec.wordOracle
          (m := StateT (Bool × List (List Bool)) PMF)
          (fun q state => ProbComp.eval ((unscaledNonceCTRCipher family n).cpaOracle
            (blockPairValid n) (nonceCTRValidNonce id n) k b q state))
          ((), frame z2 ++ frame m1 ++ BitString.lowBits n 1) (true, [BitString.lowBits n 0]) =
          PMF.pure (true :: (unscaledNonceCTRCipher family n).encrypt k
            ((MessagePair.mk z2 m1).select b) () (BitString.lowBits n 1),
            (true, [BitString.lowBits n 1, BitString.lowBits n 0])) := by
        rw [show ((), frame z2 ++ frame m1 ++ BitString.lowBits n 1) =
            NonceCipher.unitCPACodec.encodeQuery (⟨z2, m1⟩, (), BitString.lowBits n 1) from rfl,
          NonceCipher.unitCPACodec.wordOracle_encodeQuery]
        change (ProbComp.eval ((unscaledNonceCTRCipher family n).cpaOracle
            (blockPairValid n) (nonceCTRValidNonce id n) k b
            (⟨z2, m1⟩, (), BitString.lowBits n 1) (true, [BitString.lowBits n 0]))).map
            (fun p => (encOption encBits p.1, p.2)) = _
        simp [NonceCipher.cpaOracle, hv1, hvn1, hnonceNe, ProbComp.eval_pure]
      rw [hcall0]
      simp only [PMF.pure_map, PMF.pure_bind, Prod.map, id_eq]
      rw [hcall1]
      simp only [PMF.pure_map, PMF.pure_bind, Prod.map, id_eq]
      have hr1Take : (true :: (y₀ ++ y₁)).take (2 * n + 1) = true :: (y₀ ++ y₁) :=
        List.take_of_length_le (by simp [y₀, y₁, hyLen, Nat.two_mul])
      have hr1Block : (((true :: (y₀ ++ y₁)).take (2 * n + 1)).drop 1).drop n = y₁ := by
        rw [hr1Take, List.drop_succ_cons, List.drop_zero, List.drop_left' (hyLen 0)]
      rw [hr1Block]
      cases b
      · have hct1False :
            (unscaledNonceCTRCipher family n).encrypt k z2 () (BitString.lowBits n 1) =
              y₁ ++ y₂ := by
          have hlenKs1 : (y₁ ++ y₂).length = 2 * n := by
            simp [y₁, y₂, hyLen, Nat.two_mul]
          rw [unscaledNonceCTRCipher, nonceStreamCipher_encrypt_eq]
          simp only [z2, List.length_replicate, hdiv2, hks1]
          rw [xorWithStream_eq_zipWith (by simp [hlenKs1]), ← hlenKs1]
          exact zipWith_xor_replicate_false (y₁ ++ y₂)
        have hr2Take : (true :: (y₁ ++ y₂)).take (2 * n + 1) = true :: (y₁ ++ y₂) :=
          List.take_of_length_le (by simp [y₁, y₂, hyLen, Nat.two_mul])
        dsimp only [MessagePair.select, cond]
        rw [hct1False, hr2Take, List.drop_succ_cons, List.drop_zero, List.take_left' (hyLen 1)]
        dsimp only [y₁]
        simp
      · have hct1True :
            (unscaledNonceCTRCipher family n).encrypt k m1 () (BitString.lowBits n 1) =
              List.zipWith Bool.xor (List.replicate n true) y₁ ++ y₂ := by
          have hlenKs1 : (y₁ ++ y₂).length = m1.length := by
            simp [m1, y₁, y₂, hyLen]
          have hm1Len : m1.length = 2 * n := by simp [m1, Nat.two_mul]
          rw [unscaledNonceCTRCipher, nonceStreamCipher_encrypt_eq, hm1Len, hdiv2, hks1,
            xorWithStream_eq_zipWith hlenKs1]
          dsimp only [m1]
          rw [List.zipWith_append (by simp [y₁, hyLen]), ← hyLen 2,
            zipWith_xor_replicate_false y₂]
        have hxorLen : (List.zipWith Bool.xor (List.replicate n true) y₁).length = n := by
          simp [y₁, hyLen]
        have hr2Take :
            (true :: (List.zipWith Bool.xor (List.replicate n true) y₁ ++ y₂)).take (2 * n + 1) =
              true :: (List.zipWith Bool.xor (List.replicate n true) y₁ ++ y₂) :=
          List.take_of_length_le (by simp [hxorLen, y₂, hyLen, Nat.two_mul])
        have hy1NeNil : y₁ ≠ [] := by
          intro hnil
          have hlen1 : y₁.length = n := hyLen 1
          rw [hnil] at hlen1
          simp at hlen1
          omega
        have hneBlock : List.zipWith Bool.xor (List.replicate n true) y₁ ≠ y₁ := by
          have hlen1 : y₁.length = n := hyLen 1
          rw [← hlen1]
          exact zipWith_xor_replicate_true_ne y₁ hy1NeNil
        dsimp only [MessagePair.select, cond]
        rw [hct1True, hr2Take, List.drop_succ_cons, List.drop_zero, List.take_left' hxorLen,
          beq_eq_false_iff_ne.mpr hneBlock]
        simp
    · exact PMF.bind_const _ _
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
  have hneg := hcpa unscaledNonceCTRAdversary isOraclePPT_unscaledNonceCTRAdversary
  have hshift := hneg.shift 1
  have hconst : Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
    hshift.congr fun n =>
      advantage_cpaExperiment_unscaledNonceCTRAdversary hlen (Nat.succ_pos n)
  exact not_negligible_const one_ne_zero hconst

end Cslib.Crypto
