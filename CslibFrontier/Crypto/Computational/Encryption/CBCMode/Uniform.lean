/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CBCMode
public import CslibFrontier.Crypto.Computational.Encryption.IVStream.Reduction
public import CslibFrontier.Crypto.Computational.PseudorandomPermutation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Cipher block chaining with a random IV from a uniform block cipher

Cipher block chaining (CBC) with a random initialization vector ([BonehShoup2023], Section 5.4.3,
printed p. 194) encrypts a message of `v` blocks `m[0], …, m[v - 1]` under a key `k` by drawing a
uniform initial value `c[0] = iv` and computing `c[j + 1] = E(k, c[j] ⊕ m[j])`, outputting
`c[0] ++ c[1] ++ … ++ c[v]`; decryption recovers `m[j] = c[j] ⊕ D(k, c[j + 1])`. Unlike CTR and OFB
modes, CBC decryption applies the block cipher's inverse `D`, so the cipher
(`BlockCipher.cbcEncrypt`, `BlockCipher.cbcDecrypt`) is parameterized by an arbitrary uniform
`E : BlockCipher` with key length `E.keyLen n` and block length `E.blockLen n` (with no `id`
restriction on either schedule), built from the width-parameterized core `cbcWordEncrypt` and
`cbcWordDecrypt` via `ivModeEncrypt` and `ivModeDecrypt` with the chained bodies `cbcWordBody` and
`cbcWordDecBody` (truncating each step output to the block width so encryption and decryption are
polynomial-time on arbitrary keys, which changes nothing on valid outputs).

Security is many-query left-or-right CPA security (`SymmetricINDCPAOn`, Attack Game 5.2 and
Definition 5.2) on equal-length pairs of whole blocks (`blockPairValid`), in the standard model,
against uniform strict oracle-PPT adversaries. For a `BlockCipher` `E`, the distinguisher
`E.cbcToPrpDistinguisher adversary bit` runs `ivModeToPrfDistinguisher cbcBodyQueries` at block
width `E.blockLen n` on `adversary n []`, answering each admissible pair by drawing a uniform
`E.blockLen n`-bit initial value and querying its encryption oracle sequentially on `c[j] ⊕ m[j]`.

1. `E.cbcToPrpDistinguisher adversary bit` is uniform strict oracle PPT whenever the adversary is
   (`BlockCipher.isOraclePPT_cbcToPrpDistinguisher`).
2. Against `E.prpRealGame`, it has the exact output law of `adversary` in the random-IV CBC CPA
   game for `E.cbcEncrypt` with challenge bit `bit`
   (`BlockCipher.eval_prpRealGame_cbcToPrpDistinguisher`).
3. Against a uniform random permutation, for an adversary whose requests have at most `L` bits, it
   has the output law of the typed CBC experiment (`CBCMode.lean`), giving the concrete block-cipher
   bound `BlockCipher.advantage_cbcEncrypt_le` (after Theorem 5.4, (5.22)) and the asymptotic CPA
   security theorem `BlockCipher.PRP.indcpa_cbcEncrypt` ([BonehShoup2023], Theorem 5.4, for any
   `E : BlockCipher` with `E.PRP` and super-polynomial block space
   `Negligible fun n => ((2 : ℝ≥0) ^ E.blockLen n)⁻¹`).

## Deviations from Theorem 5.4

* **Any number of whole blocks.** Section 5.4.3 fixes a poly-bounded `ℓ` and the message space
  `X^{≤ℓ}`. Here `blockPairValid` admits equal-length pairs of any number of whole
  `E.blockLen n`-bit blocks, which implies the statement for every `ℓ` (a PPT adversary can only
  write polynomially long requests).
* **Two fixed-bit distinguishers and a cruder collision term.** As in
  `CslibFrontier/Crypto/Computational/Encryption/CTRMode/Uniform.lean` and
  `CslibFrontier/Crypto/Computational/Encryption/OFBMode/Uniform.lean`,
  `BlockCipher.advantage_cbcEncrypt_le` sums the PRP advantages of the `false` and `true`
  distinguishers instead of one coin-flipping distinguisher with factor `2`, and bounds the total
  encrypted blocks of `Q` requests of at most `L` bits by `Q * L`, giving the additive term
  `4 * ((Q * L).choose 2 / 2 ^ E.blockLen n)` rather than `(5.22)`'s `2 Q ^ 2 ℓ ^ 2 / N` for `ℓ`
  blocks per request.
* **Uniform strict oracle-PPT adversaries** in place of concrete/circuit adversaries, following the
  asymptotic reading of [BonehShoup2023], Sections 2.3 and 4.1.5.

## Main definitions

* `Cslib.Crypto.cbcWordBody`, `Cslib.Crypto.cbcWordDecBody`: the CBC encryption and decryption
  bodies after the initial value.
* `Cslib.Crypto.cbcWordEncrypt`, `Cslib.Crypto.cbcWordDecrypt`: width-parameterized random-IV CBC
  encryption and decryption core.
* `Cslib.Crypto.BlockCipher.cbcEncrypt`, `Cslib.Crypto.BlockCipher.cbcDecrypt`: random-IV CBC
  encryption and decryption for an arbitrary `BlockCipher`.
* `Cslib.Crypto.cbcBodyStep`, `Cslib.Crypto.cbcBodyQueries`: the CBC body computed from a word
  oracle.
* `Cslib.Crypto.BlockCipher.cbcToPrpDistinguisher`: the certified word-oracle block-cipher
  reduction.

## Main results

* `Cslib.Crypto.cbcWordDecrypt_cbcWordEncrypt`,
  `Cslib.Crypto.BlockCipher.cbcDecrypt_cbcEncrypt`: round-trip decryption correctness.
* `Cslib.Crypto.BlockCipher.isPPTOn_cbcEncrypt`,
  `Cslib.Crypto.BlockCipher.computableInPolyTime_cbcDecrypt`: efficiency of the honest algorithms.
* `Cslib.Crypto.run_cbcBodyQueries`: `cbcBodyQueries` computes `cbcWordBody` against any
  deterministic oracle.
* `Cslib.Crypto.BlockCipher.isOraclePPT_cbcToPrpDistinguisher`: the reduction is uniform strict
  oracle PPT.
* `Cslib.Crypto.BlockCipher.eval_prpRealGame_cbcToPrpDistinguisher`: exact real-game bridge.
* `Cslib.Crypto.BlockCipher.advantage_cbcEncrypt_le`: concrete word-level CPA bound (after
  Theorem 5.4, (5.22)).
* `Cslib.Crypto.BlockCipher.PRP.indcpa_cbcEncrypt`: CBC mode with a random IV is CPA-secure for any
  `BlockCipher.PRP` with super-polynomial block space ([BonehShoup2023], Theorem 5.4).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.3 (Attack Game 5.2 and Definition 5.2, printed pp. 181–182), Section 5.4.3 (random-IV
  CBC, Theorem 5.4 and equation (5.22), printed pp. 194–199), and Section 4.4.3 (Theorems 4.4 and
  4.6 and Corollary 4.5, printed pp. 134–136).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-! ### The cipher -/

/-- The CBC ciphertext body (after the initial value `iv`) of the `msg.length / n` blocks of `msg`
under `encFamily k`: starting from `(iv, [])`, XOR the current chaining block with the next `n`-bit
message block, apply `encFamily k` truncated to `n` bits, and append it to the body so far. -/
@[expose]
def cbcWordBody (encFamily : List Bool → List Bool → List Bool) (n : ℕ) (k iv msg : List Bool) :
    List Bool :=
  ((BitString.listRows (msg.length / n) n msg).foldl
    (fun (prev, acc) block =>
      let c := (encFamily k (List.zipWith xor prev block)).take n
      (c, acc ++ c))
    (iv, [])).2

/-- Random-IV CBC encryption ([BonehShoup2023], Section 5.4.3, printed pp. 194–195): draw a uniform
`n`-bit initial value `iv` and output `iv` followed by `cbcWordBody encFamily n k iv msg`. -/
@[expose]
noncomputable def cbcWordEncrypt (encFamily : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → ProbComp (List Bool) :=
  ivModeEncrypt (cbcWordBody encFamily)

/-- The CBC decryption body (from initial value `iv` and ciphertext body `body`): recover each
`n`-bit plaintext block as the XOR of the previous ciphertext block with `decFamily k` of the
current ciphertext block (truncated to `n` bits). -/
@[expose]
def cbcWordDecBody (decFamily : List Bool → List Bool → List Bool) (n : ℕ)
    (k iv body : List Bool) : List Bool :=
  ((BitString.listRows (body.length / n) n body).foldl
    (fun (prev, acc) block =>
      (block, acc ++ List.zipWith xor prev ((decFamily k block).take n)))
    (iv, [])).2

/-- Random-IV CBC decryption ([BonehShoup2023], Section 5.4.3, printed p. 194): accept an `n`-bit
initial value followed by whole `n`-bit ciphertext blocks (`ivModeDecrypt`), and recover the
plaintext blocks via `cbcWordDecBody`. Malformed ciphertexts (shorter than `n` bits, or whose body
is not a multiple of `n` bits) return `none`. -/
@[expose]
def cbcWordDecrypt (decFamily : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → Option (List Bool) :=
  ivModeDecrypt (cbcWordDecBody decFamily)

/-- Block-list representation of the CBC encryption chain under `g`. -/
private def cbcChainWords (g : List Bool → List Bool) (n : ℕ) :
    List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prev, m :: ms =>
    let c := (g (List.zipWith xor prev m)).take n
    c :: cbcChainWords g n c ms

private theorem foldl_cbcStep_eq (g : List Bool → List Bool) (n : ℕ) (prev acc : List Bool)
    (ms : List (List Bool)) :
    (ms.foldl
      (fun (p, a) block =>
        let c := (g (List.zipWith xor p block)).take n
        (c, a ++ c))
      (prev, acc)).2 =
      acc ++ (cbcChainWords g n prev ms).flatten := by
  induction ms generalizing prev acc with
  | nil => simp [cbcChainWords]
  | cons m ms ih =>
    simp only [List.foldl_cons, cbcChainWords, List.flatten_cons]
    rw [ih, List.append_assoc]

private theorem cbcWordBody_eq_flatten_cbcChainWords
    (encFamily : List Bool → List Bool → List Bool) (n : ℕ) (k iv msg : List Bool) :
    cbcWordBody encFamily n k iv msg =
      (cbcChainWords (encFamily k) n iv (BitString.listRows (msg.length / n) n msg)).flatten := by
  rw [cbcWordBody, foldl_cbcStep_eq, List.nil_append]

private theorem length_cbcChainWords {g : List Bool → List Bool} {n : ℕ} (prev : List Bool)
    (ms : List (List Bool)) :
    (cbcChainWords g n prev ms).length = ms.length := by
  induction ms generalizing prev with
  | nil => rfl
  | cons m ms ih => simp [cbcChainWords, ih]

private theorem length_of_mem_cbcChainWords {g : List Bool → List Bool} {n : ℕ}
    (hg : ∀ x : List Bool, x.length = n → (g x).length = n)
    {prev : List Bool} (hprev : prev.length = n) {ms : List (List Bool)}
    (hms : ∀ m ∈ ms, m.length = n) {c : List Bool} (hc : c ∈ cbcChainWords g n prev ms) :
    c.length = n := by
  induction ms generalizing prev with
  | nil => simp [cbcChainWords] at hc
  | cons m ms ih =>
    have hm : m.length = n := hms m List.mem_cons_self
    have hxor : (List.zipWith xor prev m).length = n := by simp [hprev, hm]
    have hgLen : (g (List.zipWith xor prev m)).length = n := hg _ hxor
    have hc' : ((g (List.zipWith xor prev m)).take n).length = n := by simp [hgLen]
    simp only [cbcChainWords, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hc'
    · exact ih hc' (fun b hb => hms b (List.mem_cons_of_mem _ hb)) hc

private theorem foldl_cbcDecStep_cbcChainWords {g gInv : List Bool → List Bool} {n : ℕ}
    (hg : ∀ x : List Bool, x.length = n → (g x).length = n)
    (hinv : ∀ x : List Bool, x.length = n → gInv (g x) = x)
    {prev : List Bool} (hprev : prev.length = n) (acc : List Bool) {ms : List (List Bool)}
    (hms : ∀ m ∈ ms, m.length = n) :
    ((cbcChainWords g n prev ms).foldl
      (fun (p, a) block => (block, a ++ List.zipWith xor p ((gInv block).take n)))
      (prev, acc)).2 = acc ++ ms.flatten := by
  induction ms generalizing prev acc with
  | nil => simp [cbcChainWords]
  | cons m ms ih =>
    have hm : m.length = n := hms m List.mem_cons_self
    have hxor : (List.zipWith xor prev m).length = n := by simp [hprev, hm]
    have hgLen : (g (List.zipWith xor prev m)).length = n := hg _ hxor
    have htakeC : (g (List.zipWith xor prev m)).take n = g (List.zipWith xor prev m) :=
      List.take_of_length_le hgLen.le
    have hdec : (gInv (g (List.zipWith xor prev m))).take n = List.zipWith xor prev m := by
      rw [hinv _ hxor, List.take_of_length_le hxor.le]
    have hrec : List.zipWith xor prev (List.zipWith xor prev m) = m :=
      BitString.zipWith_xor_self_left prev m (hprev.trans hm.symm)
    simp only [cbcChainWords, List.foldl_cons, htakeC, hdec, hrec, List.flatten_cons]
    rw [ih hgLen (acc ++ m) fun b hb => hms b (List.mem_cons_of_mem _ hb), List.append_assoc]

/-- **Decryption inverts encryption** on whole-block messages whenever `encFamily k` preserves
`n`-bit blocks and `decFamily k` left-inverts `encFamily k` on `n`-bit blocks. -/
theorem cbcWordDecrypt_cbcWordEncrypt {encFamily decFamily : List Bool → List Bool → List Bool}
    {n : ℕ} {k : List Bool}
    (hlen : ∀ block : List Bool, block.length = n → (encFamily k block).length = n)
    (hinv : ∀ block : List Bool, block.length = n → decFamily k (encFamily k block) = block)
    {msg : List Bool} (hmsg : msg.length % n = 0)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (cbcWordEncrypt encFamily n k msg)).support) :
    cbcWordDecrypt decFamily n k ct = some msg := by
  set ms := BitString.listRows (msg.length / n) n msg
  have hms : ∀ m ∈ ms, m.length = n := fun _ hm => BitString.length_of_mem_listRows hm
  have hbodyLen (iv : List Bool) (hivLen : iv.length = n) :
      (cbcWordBody encFamily n k iv msg).length = msg.length := by
    set cs := cbcChainWords (encFamily k) n iv ms
    have hcs : ∀ c ∈ cs, c.length = n := fun _ hc => length_of_mem_cbcChainWords hlen hivLen hms hc
    rw [cbcWordBody_eq_flatten_cbcChainWords, List.length_flatten, List.map_congr_left hcs,
      List.map_const', List.sum_replicate_nat, length_cbcChainWords, BitString.length_listRows,
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)]
  refine ivModeDecrypt_ivModeEncrypt hbodyLen (fun iv hivLen => ?_) hmsg hct
  set cs := cbcChainWords (encFamily k) n iv ms
  have hcs : ∀ c ∈ cs, c.length = n := fun _ hc => length_of_mem_cbcChainWords hlen hivLen hms hc
  have hcsLen : cs.length = msg.length / n := by simp [cs, length_cbcChainWords, ms]
  have hbodyEq : cbcWordBody encFamily n k iv msg = cs.flatten :=
    cbcWordBody_eq_flatten_cbcChainWords encFamily n k iv msg
  have hflatLen : cs.flatten.length = msg.length := hbodyEq ▸ hbodyLen iv hivLen
  rw [hbodyEq, cbcWordDecBody, hflatLen, ← hcsLen,
    BitString.listRows_flatten cs hcs, foldl_cbcDecStep_cbcChainWords hlen hinv hivLen [] hms,
    List.nil_append]
  exact BitString.flatten_listRows_of_length
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)).symm

/-- Random-IV CBC encryption for an arbitrary uniform `BlockCipher` `E` ([BonehShoup2023],
Section 5.4.3, printed p. 194): at parameter `n`, draw a uniform `E.blockLen n`-bit initial
value `iv` and output `iv` followed by `cbcWordBody (E.encrypt n) (E.blockLen n) k iv msg`. -/
@[expose]
noncomputable def BlockCipher.cbcEncrypt (E : BlockCipher) (n : ℕ) (k msg : List Bool) :
    ProbComp (List Bool) :=
  ivModeEncrypt (cbcWordBody (E.encrypt n)) (E.blockLen n) k msg

/-- Random-IV CBC decryption for an arbitrary uniform `BlockCipher` `E` ([BonehShoup2023],
Section 5.4.3, printed p. 194): accept an `E.blockLen n`-bit initial value followed by whole
`E.blockLen n`-bit ciphertext blocks (`ivModeDecrypt`), and recover the plaintext blocks via
`cbcWordDecBody (E.decrypt n)`. -/
@[expose]
def BlockCipher.cbcDecrypt (E : BlockCipher) (n : ℕ) (k ct : List Bool) : Option (List Bool) :=
  ivModeDecrypt (cbcWordDecBody (E.decrypt n)) (E.blockLen n) k ct

/-- For every `BlockCipher` `E`, `E.cbcDecrypt` inverts `E.cbcEncrypt` on whole-block messages
under `E.keyLen n`-bit keys. -/
theorem BlockCipher.cbcDecrypt_cbcEncrypt (E : BlockCipher) {n : ℕ} {k : List Bool}
    (hk : k.length = E.keyLen n) {msg : List Bool} (hmsg : msg.length % E.blockLen n = 0)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (E.cbcEncrypt n k msg)).support) :
    E.cbcDecrypt n k ct = some msg :=
  cbcWordDecrypt_cbcWordEncrypt (fun block hb => E.length_encrypt n k block hk hb)
    (fun block hb => E.decrypt_encrypt n k block hk hb) hmsg hct

/-! ### Efficiency of the honest algorithms -/

private theorem computableInPolyTime_cbcWordBody_param
    {encFamily : ℕ → List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun ((n, k, x) : ℕ × List Bool × List Bool) => encFamily n k x)
      (encPair encUnary (encPair encBits encBits)) encBits)
    {α : Type} {input : α ↪ List Bool} {par width : α → ℕ} {k iv msg : α → List Bool}
    (hpar : ComputableInPolyTime par input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hiv : ComputableInPolyTime iv input encBits)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime
      (fun a => cbcWordBody (encFamily (par a)) (width a) (k a) (iv a) (msg a))
      input encBits := by
  let EPar := encPair encUnary (encPair encUnary encBits)
  let EState := encPair encBits encBits
  let EFold := encPair (encPair EPar EState) encBits
  have hblocks : ComputableInPolyTime
      (fun a => BitString.listRows ((msg a).length / width a) (width a) (msg a))
      input (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hmsg) hwidth)
      hwidth hmsg
  have hc : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (encFamily p.1.1.1 p.1.1.2.2 (List.zipWith xor p.1.2.1 p.2)).take p.1.1.2.1)
      EFold encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      (hpoly.comp
        ((show ComputableInPolyTime (fun p => p.1.1.1) EFold encUnary by
            dsimp only [EFold, EPar, EState]; fun_prop).prod
          ((show ComputableInPolyTime (fun p => p.1.1.2.2) EFold encBits by
              dsimp only [EFold, EPar, EState]; fun_prop).prod
            (ComputableInPolyTime.bitsZipWithInput xor
              (by dsimp only [EFold, EPar, EState]; fun_prop)
              (by dsimp only [EFold, EPar, EState]; fun_prop)))))
      (by dsimp only [EFold, EPar, EState]; fun_prop)
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        let c := (encFamily p.1.1.1 p.1.1.2.2 (List.zipWith xor p.1.2.1 p.2)).take p.1.1.2.1
        (c, p.1.2.2 ++ c))
      EFold EState :=
    hc.prod (ComputableInPolyTime.bitsAppend
      (by dsimp only [EFold, EPar, EState]; fun_prop) hc)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := EState)
    (par := fun a => (par a, width a, k a))
    (list := fun a => BitString.listRows ((msg a).length / width a) (width a) (msg a))
    (init := fun a => (iv a, ([] : List Bool)))
    (step := fun pwk (prev, acc) block =>
      let c := (encFamily pwk.1 pwk.2.2 (List.zipWith xor prev block)).take pwk.2.1
      (c, acc ++ c))
    (hpar.prod (hwidth.prod hk)) hblocks (hiv.prod (ComputableInPolyTime.const [])) hstep
    (growth := fun a => 3 * width a) ((PolyBounded.const 3).mul hwidth.polyBounded)
    (fun a (prev, acc) block _ => by
      have htake := List.length_take_le (width a)
        (encFamily (par a) (k a) (List.zipWith xor prev block))
      simp only [EState, length_encPair, encBits_apply, List.length_append]
      omega)
  exact (ComputableInPolyTime.snd encBits encBits).comp hfold

private theorem computableInPolyTime_cbcWordDecBody_param
    {decFamily : ℕ → List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun ((n, k, y) : ℕ × List Bool × List Bool) => decFamily n k y)
      (encPair encUnary (encPair encBits encBits)) encBits)
    {α : Type} {input : α ↪ List Bool} {par width : α → ℕ} {k iv body : α → List Bool}
    (hpar : ComputableInPolyTime par input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hk : ComputableInPolyTime k input encBits)
    (hiv : ComputableInPolyTime iv input encBits)
    (hbody : ComputableInPolyTime body input encBits) :
    ComputableInPolyTime
      (fun a => cbcWordDecBody (decFamily (par a)) (width a) (k a) (iv a) (body a))
      input encBits := by
  let EPar := encPair encUnary (encPair encUnary encBits)
  let EState := encPair encBits encBits
  let EFold := encPair (encPair EPar EState) encBits
  have hblocks : ComputableInPolyTime
      (fun a => BitString.listRows ((body a).length / width a) (width a) (body a))
      input (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hbody) hwidth)
      hwidth hbody
  have hplain : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        List.zipWith xor p.1.2.1 ((decFamily p.1.1.1 p.1.1.2.2 p.2).take p.1.1.2.1))
      EFold encBits :=
    ComputableInPolyTime.bitsZipWithInput xor
      (by dsimp only [EFold, EPar, EState]; fun_prop)
      (ComputableInPolyTime.bitsTakeWithInput
        (hpoly.comp
          ((show ComputableInPolyTime (fun p => p.1.1.1) EFold encUnary by
              dsimp only [EFold, EPar, EState]; fun_prop).prod
            ((show ComputableInPolyTime (fun p => p.1.1.2.2) EFold encBits by
                dsimp only [EFold, EPar, EState]; fun_prop).prod
              (by dsimp only [EFold, EPar, EState]; fun_prop))))
        (by dsimp only [EFold, EPar, EState]; fun_prop))
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (p.2, p.1.2.2 ++
          List.zipWith xor p.1.2.1 ((decFamily p.1.1.1 p.1.1.2.2 p.2).take p.1.1.2.1)))
      EFold EState :=
    (show ComputableInPolyTime (fun p => p.2) EFold encBits by
      dsimp only [EFold, EPar, EState]; fun_prop).prod
      (ComputableInPolyTime.bitsAppend (by dsimp only [EFold, EPar, EState]; fun_prop) hplain)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := EState)
    (par := fun a => (par a, width a, k a))
    (list := fun a => BitString.listRows ((body a).length / width a) (width a) (body a))
    (init := fun a => (iv a, ([] : List Bool)))
    (step := fun pwk (prev, acc) block =>
      (block, acc ++ List.zipWith xor prev ((decFamily pwk.1 pwk.2.2 block).take pwk.2.1)))
    (hpar.prod (hwidth.prod hk)) hblocks (hiv.prod (ComputableInPolyTime.const [])) hstep
    (growth := fun a => 3 * width a) ((PolyBounded.const 3).mul hwidth.polyBounded)
    (fun a (prev, acc) block hmem => by
      have hblk : block.length = width a := BitString.length_of_mem_listRows hmem
      have htake := List.length_take_le (width a) (decFamily (par a) (k a) block)
      have hzip : (List.zipWith xor prev
          ((decFamily (par a) (k a) block).take (width a))).length ≤ width a := by
        rw [List.length_zipWith]; omega
      simp only [EState, length_encPair, encBits_apply, List.length_append, hblk]
      omega)
  exact (ComputableInPolyTime.snd encBits encBits).comp hfold

/-- For every `BlockCipher` `E`, `E.cbcEncrypt` is uniformly strict PPT in `(n, k, msg)`. -/
theorem BlockCipher.isPPTOn_cbcEncrypt (E : BlockCipher) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => E.cbcEncrypt n k msg) := by
  let EIn := encPair (encKeyedInput encBits) encBits
  have hn : ComputableInPolyTime (fun p : (ℕ × List Bool × List Bool) × List Bool => p.1.1)
      EIn encUnary := by dsimp only [EIn]; fun_prop
  have hbody := computableInPolyTime_cbcWordBody_param E.encrypt_polyTime
    (k := fun p => p.1.2.1) (iv := fun p => p.2) (msg := fun p => p.1.2.2) hn
    (E.blockLen_polyTime.comp hn)
    (by dsimp only [EIn, encKeyedInput]; fun_prop) (by dsimp only [EIn]; fun_prop)
    (by dsimp only [EIn, encKeyedInput]; fun_prop)
  have hpost : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        p.2 ++ cbcWordBody (E.encrypt p.1.1) (E.blockLen p.1.1) p.1.2.1 p.2 p.1.2.2)
      EIn encBits :=
    ComputableInPolyTime.bitsAppend (by dsimp only [EIn]; fun_prop) hbody
  exact (ComputableInPolyTime.sampleList
    (E.blockLen_polyTime.comp
      ((ComputableInPolyTime.fst _ _).comp
        (by dsimp only [encKeyedInput]; exact ComputableInPolyTime.id')))).bind_with hpost.isPPTOn

/-- For every `BlockCipher` `E`, `E.cbcDecrypt` is computable in polynomial time on `(n, k, ct)`. -/
theorem BlockCipher.computableInPolyTime_cbcDecrypt (E : BlockCipher) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => E.cbcDecrypt n k ct)
      (encKeyedInput encBits) (encOption encBits) := by
  let EIn := encKeyedInput encBits
  have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) EIn encUnary := by
    dsimp only [EIn, encKeyedInput]; fun_prop
  have hw : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => E.blockLen p.1)
      EIn encUnary :=
    E.blockLen_polyTime.comp hn
  have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) EIn encBits := by
    dsimp only [EIn, encKeyedInput]; fun_prop
  have hcond : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        decide (E.blockLen p.1 ≤ p.2.2.length) &&
          ((p.2.2.length - E.blockLen p.1) % E.blockLen p.1 == 0))
      EIn encBool := by
    polytime
  have hdec := computableInPolyTime_cbcWordDecBody_param E.decrypt_polyTime
    (k := fun p => p.2.1) hn hw
    (by dsimp only [EIn, encKeyedInput]; fun_prop)
    (ComputableInPolyTime.bitsTakeWithInput hct hw)
    (ComputableInPolyTime.bitsDropWithInput hct hw)
  unfold BlockCipher.cbcDecrypt ivModeDecrypt
  exact ComputableInPolyTime.ite hcond
    ((ComputableInPolyTime.optionSome encBits).comp hdec)
    (ComputableInPolyTime.const none)

/-! ### Certified word-oracle reduction -/

/-- One CBC encryption query step: send the XOR of the chaining block `prev` and the next message
block to the function oracle, keep at most `n` bits of the reply as the next chaining block, and
append it to the ciphertext body so far. -/
def cbcBodyStep (n : ℕ) :
    List (List Bool) × List Bool × List Bool →
      WordOracleComp Unit (List (List Bool) × List Bool × List Bool)
  | (blocks, prev, acc) =>
    (fun c => (blocks.tail, c, acc ++ c)) <$>
      (List.take n <$>
        ProbOracleComp.query ((), List.zipWith xor prev (blocks.headD [])))

/-- The CBC ciphertext body of `msg` from initial value `iv`, computed with one query to the
function oracle per `n`-bit block. -/
def cbcBodyQueries (n : ℕ) (iv msg : List Bool) : WordOracleComp Unit (List Bool) :=
  let blocks := BitString.listRows (msg.length / n) n msg
  (fun (_, _, acc) => acc) <$> OracleComp.iterate blocks.length (cbcBodyStep n) (blocks, iv, [])

/-- The width-parameterized word-oracle distinguisher built from a left-or-right CPA adversary
against random-IV CBC mode: run the adversary and answer each admissible whole-block pair
`(m₀, m₁)` by drawing a uniform `n`-bit initial value `iv` and computing the CBC ciphertext body of
the selected message via `cbcBodyQueries`; inadmissible requests are answered with `[]` and no
query. -/
private noncomputable abbrev cbcToPrfDistinguisher (adversary : OracleDistinguisher) (bit : Bool) :
    OracleDistinguisher :=
  ivModeToPrfDistinguisher cbcBodyQueries adversary bit

/-- Answered by any deterministic oracle `g`, `cbcBodyQueries` computes `cbcWordBody` for `g`. -/
theorem run_cbcBodyQueries {n : ℕ} (g : List Bool → List Bool) (iv msg : List Bool) :
    (cbcBodyQueries n iv msg).run (fun request => pure (g request.2)) =
      pure (cbcWordBody (fun _ x => g x) n [] iv msg) := by
  have hloop (xs : List (List Bool)) (prev acc : List Bool) :
      ProbOracleComp.run (OracleComp.iterate xs.length (cbcBodyStep n) (xs, prev, acc))
        (fun request => pure (g request.2)) =
      pure ([], xs.foldl
        (fun (p, a) block =>
          let c := (g (List.zipWith xor p block)).take n
          (c, a ++ c))
        (prev, acc)) := by
    induction xs generalizing prev acc with
    | nil => rfl
    | cons m xs ih =>
      rw [List.length_cons, OracleComp.iterate_succ_bind, ProbOracleComp.run_bind]
      simp only [cbcBodyStep, List.headD_cons, List.tail_cons, ProbOracleComp.run_map,
        ProbOracleComp.run_query, map_pure, pure_bind, List.foldl_cons]
      exact ih _ _
  rw [cbcBodyQueries, ProbOracleComp.run_map, hloop, map_pure, cbcWordBody]

private theorem cbcChainWords_congr_of_length {g₁ g₂ : List Bool → List Bool} {n : ℕ}
    (hg₁ : ∀ x : List Bool, x.length = n → (g₁ x).length = n)
    (heq : ∀ x : List Bool, x.length = n → g₁ x = g₂ x)
    {prev : List Bool} (hprev : prev.length = n) {ms : List (List Bool)}
    (hms : ∀ m ∈ ms, m.length = n) :
    cbcChainWords g₁ n prev ms = cbcChainWords g₂ n prev ms := by
  induction ms generalizing prev with
  | nil => rfl
  | cons m ms ih =>
    have hm : m.length = n := hms m List.mem_cons_self
    have hxor : (List.zipWith xor prev m).length = n := by simp [hprev, hm]
    have hgLen : (g₁ (List.zipWith xor prev m)).length = n := hg₁ _ hxor
    simp only [cbcChainWords, heq _ hxor]
    congr 1
    exact ih (by simp [← heq _ hxor, hgLen]) fun b hb => hms b (List.mem_cons_of_mem _ hb)

/-- `cbcBodyQueries` is strict oracle PPT on `(1ⁿ, iv, msg)`: each step makes one `n`-truncated
oracle query and grows the encoded state by at most `3 n` bits. -/
private theorem isOraclePPTOn_cbcBodyQueries :
    IsOraclePPTOn (Operation := Unit) (encPair encUnary (encPair encBits encBits)) encBits
      (fun ((n, iv, msg) : ℕ × List Bool × List Bool) => cbcBodyQueries n iv msg) := by
  let EIn := encPair encUnary (encPair encBits encBits)
  let EState := encPair (encList encBits) (encPair encBits encBits)
  let EStep := encPair EIn EState
  have hn : ComputableInPolyTime (fun a : ℕ × List Bool × List Bool => a.1) EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hblocks : ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool => BitString.listRows (a.2.2.length / a.1) a.1 a.2.2)
      EIn (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (by dsimp only [EIn]; fun_prop) hn (by dsimp only [EIn]; fun_prop)
  have hcount : ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool =>
        (BitString.listRows (a.2.2.length / a.1) a.1 a.2.2).length)
      EIn encUnary :=
    (ComputableInPolyTime.length_list encBits).comp hblocks
  have hinit : ComputableInPolyTime
      (fun a : ℕ × List Bool × List Bool =>
        (BitString.listRows (a.2.2.length / a.1) a.1 a.2.2, a.2.1, ([] : List Bool)))
      EIn EState :=
    hblocks.prod ((show ComputableInPolyTime (fun a : ℕ × List Bool × List Bool => a.2.1)
      EIn encBits by dsimp only [EIn]; fun_prop).prod (ComputableInPolyTime.const []))
  have hquery : IsOraclePPTOn (Operation := Unit) EStep encBits
      (fun p : (ℕ × List Bool × List Bool) × (List (List Bool) × List Bool × List Bool) =>
        List.take p.1.1 <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), List.zipWith xor p.2.2.1 (p.2.1.headD []))) :=
    IsOraclePPTOn.query_take ()
      (ComputableInPolyTime.bitsZipWithInput xor
        (by dsimp only [EStep, EIn, EState]; fun_prop)
        (by dsimp only [EStep, EIn, EState]; fun_prop))
      (by dsimp only [EStep, EIn, EState]; fun_prop)
  have hstep : IsOraclePPTOn EStep EState
      (fun p : (ℕ × List Bool × List Bool) × (List (List Bool) × List Bool × List Bool) =>
        cbcBodyStep p.1.1 p.2) :=
    hquery.map_with (f := fun p c => (p.2.1.tail, c, p.2.2.2 ++ c))
      (by
        have hp := ComputableInPolyTime.id' (encIn := encPair EStep encBits)
        exact ((ComputableInPolyTime.tail (encA := encBits) (encL := encList encBits)).comp
          hp.fst'.snd'.fst').prod
          (hp.snd'.prod (ComputableInPolyTime.bitsAppend hp.fst'.snd'.snd'.snd' hp.snd')))
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth
    (stateEncoding := EState)
    (initial := fun a : ℕ × List Bool × List Bool =>
      (BitString.listRows (a.2.2.length / a.1) a.1 a.2.2, a.2.1, ([] : List Bool)))
    (count := fun a => (BitString.listRows (a.2.2.length / a.1) a.1 a.2.2).length)
    (step := fun a state => cbcBodyStep a.1 state)
    hcount hinit hstep (growth := fun a => 3 * a.1)
    ((PolyBounded.const 3).mul hn.polyBounded)
    (fun a (blocks, prev, acc) next hnext => by
      obtain ⟨c, hc, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hc
      have htailLen : (encList encBits blocks.tail).length ≤ (encList encBits blocks).length :=
        ((List.tail_sublist blocks).flatMap (frame ∘ encBits)).length_le
      have htake := List.length_take_le a.1 reply
      simp only [EState, length_encPair, encBits_apply, List.length_append]
      omega)
  exact IsOraclePPTOn.map hloop (f := fun (_, _, acc) => acc)
    (by dsimp only [EState]; fun_prop)

/-- Every supported output of `cbcBodyQueries n iv msg` has at most `msg.length` bits. -/
private theorem length_le_of_mem_support_cbcBodyQueries (n : ℕ) (iv msg reply : List Bool)
    (hreply : reply ∈ OracleComp.support (cbcBodyQueries n iv msg)) :
    reply.length ≤ msg.length := by
  unfold cbcBodyQueries at hreply
  dsimp only at hreply
  obtain ⟨⟨_, _, acc⟩, hstate, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  have hinv := OracleComp.iterate_invariant
    (invariant := fun i (_, _, a) => a.length ≤ i * n)
    (by simp)
    (fun i (blocks, prev, a) _ ha next hnext => by
      obtain ⟨c, hc, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hc
      have htake := List.length_take_le n raw
      simp only [List.length_append, Nat.succ_mul]
      omega)
    _ hstate
  simp only [BitString.length_listRows] at hinv
  exact hinv.trans (Nat.div_mul_le_self msg.length n)

/-! ### Ideal games and concrete CPA bounds -/

private theorem cbcChainWords_randomFunction_map_ofFn {n : ℕ} (f : BitString n → BitString n)
    (iv : BitString n) (ms : List (BitString n)) :
    cbcChainWords (randomFunctionOracle n f) n (List.ofFn iv) (ms.map List.ofFn) =
      (cbcEncryptBlocks f iv ms).map List.ofFn := by
  induction ms generalizing iv with
  | nil => rfl
  | cons m ms ih =>
    have hxor : List.zipWith xor (List.ofFn iv) (List.ofFn m) = List.ofFn (iv + m) :=
      (BitString.ofFn_add iv m).symm
    have horacle : (randomFunctionOracle n f (List.ofFn (iv + m))).take n =
        List.ofFn (f (iv + m)) := by
      simp [randomFunctionOracle]
    simp only [List.map_cons, cbcChainWords, hxor, horacle, cbcEncryptBlocks_cons]
    rw [ih]

private theorem cbcWordBody_randomFunction_ofFn {n : ℕ} (f : BitString n → BitString n)
    (iv : BitString n) (m : List Bool) :
    cbcWordBody (fun _ x => randomFunctionOracle n f x) n [] (List.ofFn iv) m =
      (cbcEncryptBlocks f iv (BitString.toBlocks n m)).flatMap List.ofFn := by
  rw [cbcWordBody_eq_flatten_cbcChainWords, BitString.listRows_eq_map_ofFn_toBlocks,
    cbcChainWords_randomFunction_map_ofFn, ← List.flatMap_def]

/-- Running `cbcToPrfDistinguisher` against a fixed table `f` agrees in distribution with running
`blockModeWordAdversary` against `blockModeOracle (cbcEncryptBlocks f) L bit`, when requests have
at most `L` bits. -/
private theorem eval_run_cbcToPrfDistinguisher_table (adversary : OracleDistinguisher)
    (bit : Bool) {n L : ℕ}
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L)
    (f : BitString n → BitString n) :
    ProbComp.eval (((cbcToPrfDistinguisher adversary bit) n []).run
        fun request => pure (randomFunctionOracle n f request.2)) =
      ProbComp.eval ((blockModeWordAdversary adversary n).run
        (blockModeOracle (cbcEncryptBlocks f) L bit)) := by
  let constFamily : List Bool → List Bool → List Bool :=
    fun _ query => randomFunctionOracle n f query
  have horacle (k query : List Bool) :
      prfOracle constFamily n k query = randomFunctionOracle n f query := by
    by_cases hq : query.length = n <;> simp [prfOracle, constFamily, randomFunctionOracle, hq]
  have hreal := eval_prfRealGame_ivModeToPrfDistinguisher
    (bodyQueries := cbcBodyQueries) (body := cbcWordBody constFamily) (family := constFamily)
    (fun k _ iv hiv msg _ => by
      rw [run_cbcBodyQueries, cbcWordBody_eq_flatten_cbcChainWords,
        cbcWordBody_eq_flatten_cbcChainWords]
      congr 2
      exact cbcChainWords_congr_of_length
        (fun x hx => by simp [horacle, randomFunctionOracle, hx])
        (fun x _ => horacle k x)
        hiv (fun _ hm => BitString.length_of_mem_listRows hm))
    adversary bit (n := n)
  have hreply_indep (k : List Bool) :
      symmetricCPAReplyOn blockPairValid (ivModeEncrypt (cbcWordBody constFamily)) n k bit =
        symmetricCPAReplyOn blockPairValid
          (cbcWordEncrypt (fun _ x => randomFunctionOracle n f x)) n [] bit := rfl
  simp only [prfRealGame, id_eq, horacle, symmetricCPAGameOn, hreply_indep, ProbComp.eval_bind,
    PMF.bind_const] at hreal
  rw [hreal, blockModeWordAdversary, ProbOracleComp.run_simulate]
  refine hL.eval_run_congr fun request hrequest => ?_
  unfold symmetricCPAReplyOn blockModeWordQuery
  dsimp only
  by_cases hvalid : blockPairValid n (unframe request.2) (dropFrame request.2) = true
  · have hℓ : (unframe request.2).length / n ≤ L :=
      (Nat.div_le_self _ _).trans ((length_unframe_le _).trans hrequest)
    have hsel := blockModeSelect_toBlocks bit hvalid hℓ
    simp only [hvalid, ↓reduceIte, cbcWordEncrypt, ivModeEncrypt, ProbOracleComp.run_map,
      ProbOracleComp.run_query, blockModeOracle, hsel, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, ProbComp.eval_uniform, BitString.eval_sampleList, BitString.uniformList,
      PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.pure_map,
      cbcWordBody_randomFunction_ofFn]
  · simp [hvalid]

/-- Against a uniform random permutation, `cbcToPrfDistinguisher` has the output law of the typed
CBC CPA game against a uniform random permutation. -/
private theorem eval_prpIdealGame_cbcToPrfDistinguisher (adversary : OracleDistinguisher)
    (bit : Bool) {n L : ℕ}
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    ProbComp.eval (prpIdealGame id (cbcToPrfDistinguisher adversary bit) n) =
      cbcCpaGame (fun π : Equiv.Perm (BitString n) => ⇑π) L bit
        (blockModeWordAdversary adversary n) := by
  simp only [prpIdealGame, id_eq, randomPermOracle, cbcCpaGame, blockModeCpaExperiment,
    ProbComp.eval_bind]
  exact congrArg _ (funext fun π => eval_run_cbcToPrfDistinguisher_table adversary bit hL ⇑π)

/-- The block-cipher distinguisher built from a left-or-right CPA adversary against `E.cbcEncrypt`
([BonehShoup2023], proof of Theorem 5.4, adversary `B`): run `ivModeToPrfDistinguisher
cbcBodyQueries` at block width `E.blockLen n` on `adversary n []`. -/
noncomputable def BlockCipher.cbcToPrpDistinguisher (E : BlockCipher)
    (adversary : OracleDistinguisher) (bit : Bool) : OracleDistinguisher :=
  fun n aux => cbcToPrfDistinguisher (fun _ _ => adversary n []) bit (E.blockLen n) aux

/-- **Efficiency of the block-cipher reduction.** For every `BlockCipher` `E` and every uniform
strict oracle-PPT adversary, `E.cbcToPrpDistinguisher adversary bit` is uniform strict oracle
PPT. -/
theorem BlockCipher.isOraclePPT_cbcToPrpDistinguisher (E : BlockCipher)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (E.cbcToPrpDistinguisher adversary bit) :=
  isOraclePPT_ivModeToPrfDistinguisher_blockLen E.blockLen_polyTime isOraclePPTOn_cbcBodyQueries
    length_le_of_mem_support_cbcBodyQueries hadversary bit

/-- **Real block-cipher game.** Against `E.prpRealGame`, `E.cbcToPrpDistinguisher adversary bit` has
the exact output law of `adversary` in the random-IV CBC CPA game for `E.cbcEncrypt` with challenge
bit `bit`. -/
theorem BlockCipher.eval_prpRealGame_cbcToPrpDistinguisher (E : BlockCipher)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary bit) n) =
      ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (E.blockLen m))
        (fun m => BitString.sampleList (E.keyLen m)) E.cbcEncrypt adversary bit n) := by
  simp only [BlockCipher.prpRealGame, symmetricCPAGameOn, ProbComp.eval_bind,
    BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun k hk => ?_
  have hkLen : k.length = E.keyLen n := BitString.length_of_mem_support_uniformList hk
  let w := E.blockLen n
  let constFamily : List Bool → List Bool → List Bool := fun _ query => E.prpOracle n k query
  have horacle (k' query : List Bool) :
      prfOracle constFamily w k' query = E.prpOracle n k query := by
    by_cases hq : query.length = w <;> simp [prfOracle, BlockCipher.prpOracle, constFamily, w, hq]
  have hreal := eval_prfRealGame_ivModeToPrfDistinguisher
    (bodyQueries := cbcBodyQueries)
    (body := fun m _ iv msg => cbcWordBody (E.encrypt n) m k iv msg)
    (family := constFamily) (n := w)
    (fun k' _ iv hiv msg _ => by
      rw [show (fun request : Unit × List Bool => pure (prfOracle constFamily w k' request.2)) =
          fun request => pure (E.prpOracle n k request.2) by
        funext request; rw [horacle]]
      rw [run_cbcBodyQueries, cbcWordBody_eq_flatten_cbcChainWords,
        cbcWordBody_eq_flatten_cbcChainWords]
      congr 2
      exact cbcChainWords_congr_of_length
        (fun x hx => by
          simpa [BlockCipher.prpOracle, w, hx] using E.length_encrypt n k x hkLen hx)
        (fun x hx => by simp [BlockCipher.prpOracle, w, hx])
        hiv (fun _ hm => BitString.length_of_mem_listRows hm))
    (fun _ _ => adversary n []) bit
  have hreply_indep (k' : List Bool) :
      symmetricCPAReplyOn blockPairValid
          (ivModeEncrypt fun m _ iv msg => cbcWordBody (E.encrypt n) m k iv msg) w k' bit =
        symmetricCPAReplyOn (fun m => blockPairValid (E.blockLen m)) E.cbcEncrypt n k bit := rfl
  simp only [prfRealGame, id_eq, horacle, symmetricCPAGameOn, hreply_indep, ProbComp.eval_bind,
    BitString.eval_sampleList, PMF.bind_const] at hreal
  exact hreal

/-- **Concrete word-level CPA bound for random-IV CBC mode**, after [BonehShoup2023], Theorem 5.4,
(5.22). For any `BlockCipher` `E`, an adversary at parameter `n` making at most `Q` requests of at
most `L` bits has CPA advantage against `E.cbcEncrypt` at most the PRP advantages of
`E.cbcToPrpDistinguisher adversary false` and `E.cbcToPrpDistinguisher adversary true` plus
`4 * ((Q * L).choose 2 / 2 ^ E.blockLen n)`. Requests of `L` bits ask for at most `L` blocks, so
`Q * L` bounds the blocks encrypted in total. This is not the bound (5.22), which has one
distinguisher with a factor `2` and the collision term `2 Q ^ 2 ℓ ^ 2 / N` for `ℓ` blocks per
request; see the module's deviations. -/
theorem BlockCipher.advantage_cbcEncrypt_le (E : BlockCipher) (adversary : OracleDistinguisher)
    {n Q L : ℕ} (hQ : (adversary n []).IsQueryBounded Q)
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (E.blockLen m))
        (fun m => BitString.sampleList (E.keyLen m)) E.cbcEncrypt adversary false n))
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (E.blockLen m))
        (fun m => BitString.sampleList (E.keyLen m)) E.cbcEncrypt adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary false) n))
        (ProbComp.eval
          (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary true) n))
        (ProbComp.eval
          (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary true) n)) : ℝ) +
      4 * (((Q * L).choose 2 : ℝ) / 2 ^ E.blockLen n) := by
  rw [← E.eval_prpRealGame_cbcToPrpDistinguisher adversary false n,
    ← E.eval_prpRealGame_cbcToPrpDistinguisher adversary true n]
  let A' : OracleDistinguisher := fun _ _ => adversary n []
  have hQ' : (A' (E.blockLen n) []).IsQueryBounded Q := hQ
  have hL' : (A' (E.blockLen n) []).QueriesSatisfy fun request => request.2.length ≤ L := hL
  have hperm := advantage_cbcCpaGame_randomPermutation_le L
    (isCostBounded_blockModeWordAdversary hQ' L)
  have hideal (bit : Bool) :
      ProbComp.eval (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary bit) n) =
        cbcCpaGame (fun π : Equiv.Perm (BitString (E.blockLen n)) => ⇑π) L bit
          (blockModeWordAdversary A' (E.blockLen n)) :=
    eval_prpIdealGame_cbcToPrfDistinguisher A' bit hL'
  rw [← hideal false, ← hideal true] at hperm
  have htri₁ : (Game.advantage
      (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary false) n))
      (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary true) n)) : ℝ) ≤
      Game.advantage
        (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary false) n))
        (ProbComp.eval (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary false) n)) +
      Game.advantage
        (ProbComp.eval (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary false) n))
        (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary true) n)) := by
    exact_mod_cast Game.advantage_triangle _ _ _
  have htri₂ := advantage_le_two
    (ProbComp.eval (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary false) n))
    (ProbComp.eval (prpIdealGame E.blockLen (E.cbcToPrpDistinguisher adversary true) n))
    (ProbComp.eval (E.prpRealGame (E.cbcToPrpDistinguisher adversary true) n))
  linarith

/-! ### Asymptotic CPA security (Theorem 5.4) -/

open scoped NNReal in
/-- **Random-IV CBC mode is CPA-secure for a pseudorandom permutation** ([BonehShoup2023],
Section 5.4.3, Theorem 5.4, printed pp. 195–199): for any uniform `BlockCipher` `E` with `E.PRP`
and super-polynomial block space `Negligible fun n => ((2 : ℝ≥0) ^ E.blockLen n)⁻¹`, random-IV CBC
mode `E.cbcEncrypt` has negligible many-query left-or-right CPA advantage on equal-length pairs of
whole `E.blockLen n`-bit blocks under uniform `E.keyLen n`-bit keys, against every uniform strict
oracle-PPT adversary. -/
theorem BlockCipher.PRP.indcpa_cbcEncrypt {E : BlockCipher} (hprp : E.PRP)
    (hneg : Negligible fun n => ((2 : ℝ≥0) ^ E.blockLen n)⁻¹) :
    SymmetricINDCPAOn (fun n => blockPairValid (E.blockLen n))
      (fun n => BitString.sampleList (E.keyLen n)) E.cbcEncrypt := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let P : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (P n) := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).1
  have hl (n : ℕ) : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ P n := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).2
  have hprp₀ := hprp (E.cbcToPrpDistinguisher adversary false)
    (E.isOraclePPT_cbcToPrpDistinguisher hadversary false)
  have hprp₁ := hprp (E.cbcToPrpDistinguisher adversary true)
    (E.isOraclePPT_cbcToPrpDistinguisher hadversary true)
  negligible using fun n => E.advantage_cbcEncrypt_le adversary (hq n) (hl n)

end Cslib.Crypto
