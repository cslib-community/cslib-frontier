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
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Cipher block chaining with a random IV from a uniform PRF or block cipher

Cipher block chaining (CBC) with a random initialization vector ([BonehShoup2023], Section 5.4.3,
printed pp. 194–195) encrypts a message of `v` blocks `m[0], …, m[v - 1]` under a key `k` by
drawing a uniform `n`-bit initial value `c[0] = iv` and computing `c[j + 1] = E(k, c[j] ⊕ m[j])`,
outputting `c[0] ++ c[1] ++ … ++ c[v]`; decryption recovers `m[j] = c[j] ⊕ D(k, c[j + 1])`. Here
the security parameter `n` is the block length (`N = 2 ^ n`): keys and blocks have `n` bits. A
message is any word made of whole `n`-bit blocks. `cbcWordEncrypt` is the shared random-IV envelope
`ivModeEncrypt` with the chained body `cbcWordBody` (truncating each block-function output to at
most `n` bits so encryption is polynomial-time on arbitrary keys and families, which changes
nothing on valid `n`-bit outputs), and `cbcWordDecrypt` inverts it whenever `decFamily k`
left-inverts `encFamily k` on `n`-bit blocks (`cbcWordDecrypt_cbcWordEncrypt`, specialized to a
`BlockCipher` in `BlockCipher.cbcWordDecrypt_cbcWordEncrypt`).

Security is many-query left-or-right CPA security (`SymmetricINDCPAOn`, Attack Game 5.2) on
equal-length pairs of whole blocks (`blockPairValid`), in the standard model, against uniform
strict oracle-PPT adversaries. The word-oracle distinguisher `cbcToPrfDistinguisher adversary bit`
is `ivModeToPrfDistinguisher cbcBodyQueries adversary bit`: it runs `adversary` and answers each
admissible pair by drawing a uniform `n`-bit initial value and querying its function oracle
sequentially on `c[j] ⊕ m[j]`, keeping at most `n` bits of each reply.

1. It is uniform strict oracle PPT whenever the adversary is
   (`isOraclePPT_cbcToPrfDistinguisher`).
2. Against the keyed oracle, its output law is that of the adversary in the CBC CPA game with
   challenge bit `bit` (`eval_prfRealGame_cbcToPrfDistinguisher`).
3. Against a uniform random function (and likewise a uniform random permutation), for an adversary
   whose requests have at most `L` bits, its output law is that of the typed reduction
   `cbcReduction L bit` on `blockModeWordAdversary adversary n`
   (`eval_prfIdealGame_cbcToPrfDistinguisher`). Combining this with the typed collision and
   switching bounds of `CBCMode.lean` gives the concrete keyed PRF bound
   `advantage_cbcWordCPAGame_prf_le`, the concrete keyed block-cipher bound
   `BlockCipher.advantage_cbcWordCPAGame_le` corresponding to equation (5.22), and the asymptotic
   CPA security theorems `PseudorandomFunction.indcpa_cbcWordEncrypt` and
   `BlockCipher.PRP.indcpa_cbcWordEncrypt` (Theorem 5.4).

## Deviations from Theorem 5.4

* **`n`-bit keys and `n`-bit blocks.** At security parameter `n`, keys and blocks both have `n`
  bits, matching `PseudorandomFunction` and `BlockCipher` with `keyLen = id` and `blockLen = id`.
* **Any number of whole blocks.** Section 5.4.3 fixes a poly-bounded `ℓ` and the message space
  `X^{≤ℓ}`. Here `blockPairValid` admits equal-length pairs of any number of whole `n`-bit blocks,
  which implies the statement for every `ℓ` (a PPT adversary can only write polynomially long
  requests).
* **Two fixed-bit distinguishers and bit-length query cap.** As in
  `CslibFrontier/Crypto/Computational/Encryption/CTRMode/Uniform.lean` and
  `CslibFrontier/Crypto/Computational/Encryption/OFBMode/Uniform.lean`, the concrete bounds sum the
  advantages of `cbcToPrfDistinguisher adversary false` and
  `cbcToPrfDistinguisher adversary true` instead of one coin-flipping distinguisher with factor `2`,
  and bound the total encrypted blocks of `Q` requests of at most `L` bits by `Q * L`, giving the
  additive term `4 * ((Q * L).choose 2 / 2 ^ n)` (`≤ 2 * (Q * L) ^ 2 / 2 ^ n`, matching `(5.22)`'s
  `2 Q² ℓ² / N` when `ℓ = L`).
* **Uniform strict oracle-PPT adversaries** in place of concrete/circuit adversaries, following the
  asymptotic reading of [BonehShoup2023], Sections 2.3 and 4.1.5.

## Main definitions

* `Cslib.Crypto.cbcWordBody`: the CBC ciphertext body after the initial value.
* `Cslib.Crypto.cbcWordEncrypt`, `Cslib.Crypto.cbcWordDecrypt`: random-IV CBC encryption and
  decryption on whole-block words.
* `Cslib.Crypto.cbcBodyStep`, `Cslib.Crypto.cbcBodyQueries`: the CBC body computed from a word
  oracle.
* `Cslib.Crypto.cbcToPrfDistinguisher`: the certified word-oracle reduction.

## Main results

* `Cslib.Crypto.cbcWordDecrypt_cbcWordEncrypt`,
  `Cslib.Crypto.BlockCipher.cbcWordDecrypt_cbcWordEncrypt`: round-trip decryption correctness.
* `Cslib.Crypto.isPPTOn_cbcWordEncrypt`, `Cslib.Crypto.computableInPolyTime_cbcWordDecrypt`:
  efficiency of the honest algorithms.
* `Cslib.Crypto.isOraclePPT_cbcToPrfDistinguisher`: the reduction is uniform strict oracle PPT.
* `Cslib.Crypto.eval_prfRealGame_cbcToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfIdealGame_cbcToPrfDistinguisher`: exact real- and ideal-game bridges.
* `Cslib.Crypto.advantage_cbcWordCPAGame_prf_le`,
  `Cslib.Crypto.BlockCipher.advantage_cbcWordCPAGame_le`: concrete word-level CPA bounds (PRF form
  and block-cipher form `(5.22)`).
* `Cslib.Crypto.PseudorandomFunction.indcpa_cbcWordEncrypt`,
  `Cslib.Crypto.BlockCipher.PRP.indcpa_cbcWordEncrypt`: CBC mode with a random IV is CPA-secure
  ([BonehShoup2023], Theorem 5.4).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.3 (Attack Game 5.2 and Definition 5.2, printed pp. 181–182), Section 5.4.3 (random-IV
  CBC, Theorem 5.4 and equation (5.22), printed pp. 194–199), and Section 4.4.3 (Theorems 4.4 and
  4.6 and Corollary 4.5, printed p. 135).
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

/-- Random-IV CBC decryption ([BonehShoup2023], Section 5.4.3, printed p. 195): accept an `n`-bit
initial value followed by whole `n`-bit ciphertext blocks, and recover each plaintext block as the
XOR of the previous ciphertext block with `decFamily k` of the current ciphertext block (truncated
to `n` bits). Malformed ciphertexts (shorter than `n` bits, or whose body is not a multiple of `n`
bits) return `none`. -/
@[expose]
def cbcWordDecrypt (decFamily : List Bool → List Bool → List Bool) (n : ℕ)
    (k ct : List Bool) : Option (List Bool) :=
  if (decide (n ≤ ct.length) && ((ct.length - n) % n == 0)) = true then
    some (((BitString.listRows ((ct.length - n) / n) n (ct.drop n)).foldl
      (fun (prev, acc) block =>
        (block, acc ++ List.zipWith xor prev ((decFamily k block).take n)))
      (ct.take n, [])).2)
  else
    none

/-- `BitString.listRows (L / n) n x` is the word view of `BitString.padBlocks n L x`. -/
private theorem listRows_eq_map_ofFn_padBlocks (n L : ℕ) (x : List Bool) :
    BitString.listRows (L / n) n x = (BitString.padBlocks n L x).map List.ofFn := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  refine List.ext_getElem (by simp [BitString.listRows]) fun j hj₁ hj₂ => ?_
  simp only [BitString.listRows, List.getElem_map, List.getElem_range]
  rw [BitString.getElem_listRow (by simpa using hj₂), List.getElem_ofFn,
    BitString.padBlocks_getElem_apply n L x i (by simpa using h₁) ⟨j, by simpa using hj₂⟩]

/-- A word whose length is a multiple of `n` is the concatenation of its `msg.length / n` width-`n`
rows. -/
private theorem flatten_listRows_of_mod_eq_zero {n : ℕ} {x : List Bool} (hx : x.length % n = 0) :
    (BitString.listRows (x.length / n) n x).flatten = x := by
  rw [listRows_eq_map_ofFn_padBlocks, ← List.flatMap_def,
    BitString.flatMap_ofFn_padBlocks (Nat.dvd_of_mod_eq_zero hx)]

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

private theorem length_flatten_of_forall_length {n : ℕ} :
    ∀ {ws : List (List Bool)}, (∀ w ∈ ws, w.length = n) → ws.flatten.length = ws.length * n
  | [], _ => by simp
  | w :: ws, hws => by
    rw [List.flatten_cons, List.length_append, hws w List.mem_cons_self,
      length_flatten_of_forall_length fun u hu => hws u (List.mem_cons_of_mem _ hu),
      List.length_cons, Nat.succ_mul, Nat.add_comm]

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
  simp only [cbcWordEncrypt, ivModeEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨iv, hiv, rfl⟩ := hct
  have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
  set ms := BitString.listRows (msg.length / n) n msg
  have hms : ∀ m ∈ ms, m.length = n := fun _ hm => BitString.length_of_mem_listRows hm
  set cs := cbcChainWords (encFamily k) n iv ms
  have hcs : ∀ c ∈ cs, c.length = n := fun _ hc => length_of_mem_cbcChainWords hlen hivLen hms hc
  have hcsLen : cs.length = msg.length / n := by simp [cs, length_cbcChainWords, ms]
  have hbodyEq : cbcWordBody encFamily n k iv msg = cs.flatten :=
    cbcWordBody_eq_flatten_cbcChainWords encFamily n k iv msg
  have hbodyLen : cs.flatten.length = msg.length := by
    rw [length_flatten_of_forall_length hcs, hcsLen,
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmsg)]
  have hctLen : (iv ++ cbcWordBody encFamily n k iv msg).length = n + msg.length := by
    rw [hbodyEq, List.length_append, hivLen, hbodyLen]
  have hcond : (decide (n ≤ (iv ++ cbcWordBody encFamily n k iv msg).length) &&
      (((iv ++ cbcWordBody encFamily n k iv msg).length - n) % n == 0)) = true := by
    simp [hctLen, hmsg]
  simp only [cbcWordDecrypt, hcond, ↓reduceIte]
  congr 1
  rw [hctLen, Nat.add_sub_cancel_left, hbodyEq, ← hivLen, List.take_left, List.drop_left, hivLen,
    ← hcsLen, BitString.listRows_flatten cs hcs,
    foldl_cbcDecStep_cbcChainWords hlen hinv hivLen [] hms, List.nil_append]
  exact flatten_listRows_of_mod_eq_zero hmsg

/-- For a `BlockCipher` with `keyLen = id` and `blockLen = id`, `cbcWordDecrypt` with `E.decrypt`
inverts `cbcWordEncrypt` with `E.encrypt` on whole-block messages under `n`-bit keys. -/
theorem BlockCipher.cbcWordDecrypt_cbcWordEncrypt (E : BlockCipher)
    (hkey : E.keyLen = id) (hblock : E.blockLen = id)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {msg : List Bool} (hmsg : msg.length % n = 0)
    {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval
      (cbcWordEncrypt (fun key block => E.encrypt key.length key block) n k msg)).support) :
    cbcWordDecrypt (fun key block => E.decrypt key.length key block) n k ct = some msg :=
  Cslib.Crypto.cbcWordDecrypt_cbcWordEncrypt
    (fun block hlen => by
      simpa [hk, hblock] using E.length_encrypt k.length k block (by simp [hkey])
        (by simpa [hk, hblock] using hlen))
    (fun block hlen => by
      simpa [hk] using E.decrypt_encrypt k.length k block (by simp [hkey])
        (by simpa [hk, hblock] using hlen))
    hmsg hct

/-! ### Efficiency of the honest algorithms -/

/-- `cbcWordBody` is computable in polynomial time from `encFamily`'s evaluator: every step output
is truncated to at most `n` bits, so the encoded accumulator grows by at most `3 n` bits per
message block. -/
theorem computableInPolyTime_cbcWordBody {encFamily : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => encFamily pair.1 pair.2)
      (encPair encBits encBits) encBits)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {k iv msg : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encBits)
    (hiv : ComputableInPolyTime iv input encBits)
    (hmsg : ComputableInPolyTime msg input encBits) :
    ComputableInPolyTime (fun a => cbcWordBody encFamily (n a) (k a) (iv a) (msg a))
      input encBits := by
  let EPar := encPair encUnary encBits
  let EState := encPair encBits encBits
  let EFold := encPair (encPair EPar EState) encBits
  have hblocks : ComputableInPolyTime
      (fun a => BitString.listRows ((msg a).length / n a) (n a) (msg a))
      input (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits.comp hmsg) hn) hn hmsg
  have hc : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (encFamily p.1.1.2 (List.zipWith xor p.1.2.1 p.2)).take p.1.1.1)
      EFold encBits :=
    ComputableInPolyTime.bitsTakeWithInput
      (hpoly.comp ((show ComputableInPolyTime (fun p => p.1.1.2) EFold encBits by
          dsimp only [EFold, EPar, EState]; fun_prop).prod
        (ComputableInPolyTime.bitsZipWithInput xor
          (by dsimp only [EFold, EPar, EState]; fun_prop)
          (by dsimp only [EFold, EPar, EState]; fun_prop))))
      (by dsimp only [EFold, EPar, EState]; fun_prop)
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        let c := (encFamily p.1.1.2 (List.zipWith xor p.1.2.1 p.2)).take p.1.1.1
        (c, p.1.2.2 ++ c))
      EFold EState :=
    hc.prod (ComputableInPolyTime.bitsAppend
      (by dsimp only [EFold, EPar, EState]; fun_prop) hc)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := EState)
    (par := fun a => (n a, k a))
    (list := fun a => BitString.listRows ((msg a).length / n a) (n a) (msg a))
    (init := fun a => (iv a, ([] : List Bool)))
    (step := fun nk (prev, acc) block =>
      let c := (encFamily nk.2 (List.zipWith xor prev block)).take nk.1
      (c, acc ++ c))
    (hn.prod hk) hblocks (hiv.prod (ComputableInPolyTime.const [])) hstep
    (growth := fun a => 3 * n a) ((PolyBounded.const 3).mul hn.polyBounded)
    (fun a (prev, acc) block _ => by
      have htake := List.length_take_le (n a) (encFamily (k a) (List.zipWith xor prev block))
      simp only [EState, length_encPair, encBits_apply, List.length_append]
      omega)
  exact (ComputableInPolyTime.snd encBits encBits).comp hfold

/-- Random-IV CBC encryption is uniformly strict PPT in `(n, k, msg)`. -/
theorem isPPTOn_cbcWordEncrypt {encFamily : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => encFamily pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => cbcWordEncrypt encFamily n k msg) :=
  isPPTOn_ivModeEncrypt
    (computableInPolyTime_cbcWordBody hpoly (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop))

/-- Random-IV CBC decryption is computable in polynomial time on `(n, k, ct)`. -/
theorem computableInPolyTime_cbcWordDecrypt {decFamily : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair => decFamily pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => cbcWordDecrypt decFamily n k ct)
      (encKeyedInput encBits) (encOption encBits) := by
  let EIn := encKeyedInput encBits
  let EPar := encPair encUnary encBits
  let EState := encPair encBits encBits
  let EFold := encPair (encPair EPar EState) encBits
  have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) EIn encUnary := by
    dsimp only [EIn]; fun_prop
  have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.1) EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hcond : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        decide (p.1 ≤ p.2.2.length) && ((p.2.2.length - p.1) % p.1 == 0))
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hblocks : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        BitString.listRows ((p.2.2.length - p.1) / p.1) p.1 (p.2.2.drop p.1))
      EIn (encList encBits) :=
    ComputableInPolyTime.bitsRowsWithInput
      (by dsimp only [EIn]; fun_prop) hn (by dsimp only [EIn]; fun_prop)
  have hinit : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.2.2.take p.1, ([] : List Bool)))
      EIn EState :=
    (show ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2.take p.1)
      EIn encBits by dsimp only [EIn]; fun_prop).prod (ComputableInPolyTime.const [])
  have hplain : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        List.zipWith xor p.1.2.1 ((decFamily p.1.1.2 p.2).take p.1.1.1))
      EFold encBits :=
    ComputableInPolyTime.bitsZipWithInput xor
      (by dsimp only [EFold, EPar, EState]; fun_prop)
      (ComputableInPolyTime.bitsTakeWithInput
        (hpoly.comp ((show ComputableInPolyTime (fun p => p.1.1.2) EFold encBits by
            dsimp only [EFold, EPar, EState]; fun_prop).prod
          (by dsimp only [EFold, EPar, EState]; fun_prop)))
        (by dsimp only [EFold, EPar, EState]; fun_prop))
  have hstep : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (p.2, p.1.2.2 ++ List.zipWith xor p.1.2.1 ((decFamily p.1.1.2 p.2).take p.1.1.1)))
      EFold EState :=
    (show ComputableInPolyTime (fun p => p.2) EFold encBits by
      dsimp only [EFold, EPar, EState]; fun_prop).prod
      (ComputableInPolyTime.bitsAppend (by dsimp only [EFold, EPar, EState]; fun_prop) hplain)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBits) (encL := encList encBits) (encP := EPar) (encB := EState)
    (par := fun p : ℕ × List Bool × List Bool => (p.1, p.2.1))
    (list := fun p => BitString.listRows ((p.2.2.length - p.1) / p.1) p.1 (p.2.2.drop p.1))
    (init := fun p => (p.2.2.take p.1, ([] : List Bool)))
    (step := fun nk (prev, acc) block =>
      (block, acc ++ List.zipWith xor prev ((decFamily nk.2 block).take nk.1)))
    (hn.prod hk) hblocks hinit hstep
    (growth := fun p => 3 * p.1) ((PolyBounded.const 3).mul hn.polyBounded)
    (fun p (prev, acc) block hmem => by
      have hblk : block.length = p.1 := BitString.length_of_mem_listRows hmem
      have htake := List.length_take_le p.1 (decFamily p.2.1 block)
      have hzip : (List.zipWith xor prev ((decFamily p.2.1 block).take p.1)).length ≤ p.1 := by
        rw [List.length_zipWith]; omega
      simp only [EState, length_encPair, encBits_apply, List.length_append, hblk]
      omega)
  exact ComputableInPolyTime.ite hcond
    ((ComputableInPolyTime.optionSome encBits).comp
      ((ComputableInPolyTime.snd encBits encBits).comp hfold))
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

/-- The word-oracle distinguisher built from a left-or-right CPA adversary against random-IV CBC
mode ([BonehShoup2023], proof of Theorem 5.4, adversary `B`): run the adversary and answer each
admissible whole-block pair `(m₀, m₁)` by drawing a uniform `n`-bit initial value `iv` and
computing the CBC ciphertext body of the selected message via `cbcBodyQueries`; inadmissible
requests are answered with `[]` and no query. -/
noncomputable abbrev cbcToPrfDistinguisher (adversary : OracleDistinguisher) (bit : Bool) :
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

/-- Answered by `prfOracle family n k` under an `n`-bit key and `n`-bit initial value,
`cbcBodyQueries` computes `cbcWordBody family n k iv msg`. -/
theorem run_cbcBodyQueries_prfOracle {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {n : ℕ} {k : List Bool} (hk : k.length = n) {iv : List Bool} (hiv : iv.length = n)
    (msg : List Bool) :
    (cbcBodyQueries n iv msg).run (fun request => pure (prfOracle family n k request.2)) =
      pure (cbcWordBody family n k iv msg) := by
  rw [run_cbcBodyQueries, cbcWordBody_eq_flatten_cbcChainWords,
    cbcWordBody_eq_flatten_cbcChainWords]
  congr 2
  exact cbcChainWords_congr_of_length
    (fun x hx => by simp [prfOracle, hx, hlen k x (hx.trans hk.symm), hk])
    (fun x hx => by simp [prfOracle, hx])
    hiv (fun _ hm => BitString.length_of_mem_listRows hm)

/-- **Real game.** Against the keyed oracle, `cbcToPrfDistinguisher adversary bit` has the output
law of `adversary` in the random-IV CBC CPA game with challenge bit `bit`. -/
theorem eval_prfRealGame_cbcToPrfDistinguisher {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (cbcToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt family) adversary bit n) :=
  eval_prfRealGame_ivModeToPrfDistinguisher
    (fun _ hk _ hiv msg _ => run_cbcBodyQueries_prfOracle hlen hk hiv msg) adversary bit

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
    IsOraclePPTOn.query_take' ()
      (ComputableInPolyTime.bitsZipWithInput xor
        (by dsimp only [EStep, EIn, EState]; fun_prop)
        (by dsimp only [EStep, EIn, EState]; fun_prop))
      (by dsimp only [EStep, EIn, EState]; fun_prop)
  have hstep : IsOraclePPTOn EStep EState
      (fun p : (ℕ × List Bool × List Bool) × (List (List Bool) × List Bool × List Bool) =>
        cbcBodyStep p.1.1 p.2) :=
    hquery.map_with' (f := fun p c => (p.2.1.tail, c, p.2.2.2 ++ c))
      (by dsimp only [EStep, EIn, EState]; fun_prop)
  have hloop := IsOraclePPTOn.iterateWith_of_bounded_growth'
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
  exact hloop.map' (f := fun (_, _, acc) => acc) (by dsimp only [EState]; fun_prop)

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

/-- **Efficiency of the reduction.** For every uniform strict oracle-PPT adversary,
`cbcToPrfDistinguisher adversary bit` is uniform strict oracle PPT. -/
theorem isOraclePPT_cbcToPrfDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsOraclePPT encBool (cbcToPrfDistinguisher adversary bit) :=
  isOraclePPT_ivModeToPrfDistinguisher isOraclePPTOn_cbcBodyQueries
    length_le_of_mem_support_cbcBodyQueries hadversary bit

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
      (cbcEncryptBlocks f iv (BitString.padBlocks n m.length m)).flatMap List.ofFn := by
  rw [cbcWordBody_eq_flatten_cbcChainWords, listRows_eq_map_ofFn_padBlocks,
    cbcChainWords_randomFunction_map_ofFn, ← List.flatMap_def]

private theorem run_cbcBodyQueries_randomFunction {n : ℕ} (f : BitString n → BitString n)
    (iv : BitString n) (m : List Bool) :
    (cbcBodyQueries n (List.ofFn iv) m).run
        (fun request => pure (randomFunctionOracle n f request.2)) =
      pure ((cbcEncryptBlocks f iv (BitString.padBlocks n m.length m)).flatMap List.ofFn) := by
  rw [run_cbcBodyQueries, cbcWordBody_randomFunction_ofFn]

/-- **Ideal PRF game.** Against a uniform random function, the word reduction for an adversary
whose requests have at most `L` bits has the exact output law of the typed reduction
`cbcReduction L bit` on `blockModeWordAdversary adversary n`. -/
theorem eval_prfIdealGame_cbcToPrfDistinguisher (adversary : OracleDistinguisher)
    (bit : Bool) {n L : ℕ}
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    ProbComp.eval (prfIdealGame id id (cbcToPrfDistinguisher adversary bit) n) =
      ProbComp.eval (PRF.idealExperiment
        (cbcReduction L bit (blockModeWordAdversary adversary n))) :=
  eval_prfIdealGame_ivModeToPrfDistinguisher (ℓ := L)
    (program := cbcQueryProgram L bit) (bodyBlocks := cbcEncryptBlocks)
    (fun f q => by
      simp only [cbcQueryProgram, blockModeOracle, ProbOracleComp.run_bind,
        ProbOracleComp.run_sample, run_cbcChainQueries, pure_bind, ProbOracleComp.run_pure])
    (fun f iv m _ => run_cbcBodyQueries_randomFunction f iv m)
    adversary (hL.mono fun _ h => (Nat.div_le_self _ _).trans ((length_unframe_le _).trans h))

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
    have hsel := blockModeSelect_padBlocks bit hvalid hℓ
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

/-- **Concrete word-level PRF CPA bound for random-IV CBC mode**, after [BonehShoup2023],
Theorem 5.4. At parameter `n`, an adversary making at most `Q` requests of at most `L` bits has
CPA advantage against `cbcWordEncrypt family` at most the PRF advantages of
`cbcToPrfDistinguisher adversary false` and `cbcToPrfDistinguisher adversary true` plus
`2 * ((Q * L).choose 2 / 2 ^ n)`. -/
theorem advantage_cbcWordCPAGame_prf_le {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) {n Q L : ℕ} (hQ : (adversary n []).IsQueryBounded Q)
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt family) adversary false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt family) adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame id family (cbcToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prfIdealGame id id (cbcToPrfDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (prfRealGame id family (cbcToPrfDistinguisher adversary true) n))
        (ProbComp.eval (prfIdealGame id id (cbcToPrfDistinguisher adversary true) n)) : ℝ) +
      2 * (((Q * L).choose 2 : ℝ) / 2 ^ n) := by
  rw [← eval_prfRealGame_cbcToPrfDistinguisher hlen adversary false n,
    ← eval_prfRealGame_cbcToPrfDistinguisher hlen adversary true n]
  have hcost := isCostBounded_blockModeWordAdversary hQ L
  have h₀ := advantage_idealExperiment_cbcReduction_le L false hcost
  have h₁ := advantage_idealExperiment_cbcReduction_le L true hcost
  rw [← eval_prfIdealGame_cbcToPrfDistinguisher adversary false hL] at h₀
  rw [← eval_prfIdealGame_cbcToPrfDistinguisher adversary true hL] at h₁
  refine (advantage_le_four _
    (ProbComp.eval (prfIdealGame id id (cbcToPrfDistinguisher adversary false) n))
    (ProbComp.eval (blockModeIdealExperiment L (blockModeWordAdversary adversary n)))
    (ProbComp.eval (prfIdealGame id id (cbcToPrfDistinguisher adversary true) n)) _).trans ?_
  linarith

/-- **Concrete word-level block-cipher CPA bound for random-IV CBC mode** ([BonehShoup2023],
Theorem 5.4, equation (5.22)). For a `BlockCipher` `E` with `keyLen = id` and `blockLen = id`, an
adversary at parameter `n` making at most `Q` requests of at most `L` bits has CPA advantage
against `cbcWordEncrypt (fun k x => E.encrypt k.length k x)` at most the PRP advantages of
`cbcToPrfDistinguisher adversary false` and `cbcToPrfDistinguisher adversary true` plus
`4 * ((Q * L).choose 2 / 2 ^ n)` (`≤ 2 * (Q * L) ^ 2 / 2 ^ n`, matching `(5.22)`'s `2 Q² ℓ² / N`
with two fixed-bit distinguishers and `ℓ = L`). -/
theorem BlockCipher.advantage_cbcWordCPAGame_le (E : BlockCipher) (hkey : E.keyLen = id)
    (hblock : E.blockLen = id) (adversary : OracleDistinguisher) {n Q L : ℕ}
    (hQ : (adversary n []).IsQueryBounded Q)
    (hL : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ L) :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun k x => E.encrypt k.length k x) adversary false n))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun k x => E.encrypt k.length k x) adversary true n)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary false) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary true) n))
        (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary true) n)) : ℝ) +
      4 * (((Q * L).choose 2 : ℝ) / 2 ^ n) := by
  have hlen : ∀ key query : List Bool, query.length = key.length →
      (E.encrypt key.length key query).length = key.length := fun key query hq => by
    simpa [hblock] using E.length_encrypt key.length key query (by simp [hkey])
      (by simpa [hblock] using hq)
  have hreal (bit : Bool) :
      ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun k x => E.encrypt k.length k x) adversary bit n) =
      ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary bit) n) := by
    rw [← eval_prfRealGame_cbcToPrfDistinguisher hlen adversary bit n,
      eval_prpRealGame_eq_eval_prfRealGame hkey, hblock]
  rw [hreal false, hreal true]
  have hperm := advantage_cbcCpaGame_randomPermutation_le L
    (isCostBounded_blockModeWordAdversary hQ L)
  rw [← eval_prpIdealGame_cbcToPrfDistinguisher adversary false hL,
    ← eval_prpIdealGame_cbcToPrfDistinguisher adversary true hL, ← hblock] at hperm
  have htri₁ : (Game.advantage
      (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary false) n))
      (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary true) n)) : ℝ) ≤
      Game.advantage
        (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary false) n))
        (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary false) n)) +
      Game.advantage
        (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary false) n))
        (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary true) n)) := by
    exact_mod_cast Game.advantage_triangle _ _ _
  have htri₂ := advantage_le_two
    (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary false) n))
    (ProbComp.eval (prpIdealGame E.blockLen (cbcToPrfDistinguisher adversary true) n))
    (ProbComp.eval (E.prpRealGame (cbcToPrfDistinguisher adversary true) n))
  linarith

/-! ### Asymptotic CPA security (Theorem 5.4) -/

/-- **Random-IV CBC mode is CPA-secure for a pseudorandom function** (PRF step of
[BonehShoup2023], Section 5.4.3, Theorem 5.4): if `family` is a `PseudorandomFunction`, random-IV
CBC mode with `n`-bit blocks at security parameter `n` has negligible many-query left-or-right CPA
advantage on equal-length pairs of whole blocks, against every uniform strict oracle-PPT
adversary. -/
theorem PseudorandomFunction.indcpa_cbcWordEncrypt {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList (cbcWordEncrypt family) := by
  intro adversary hadversary
  obtain ⟨c, d, hbounds⟩ := hadversary.query_bounds
  let P : ℕ → ℕ := fun n => c * (n + 2) ^ d
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (P n) := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).1
  have hl (n : ℕ) : (adversary n []).QueriesSatisfy fun request => request.2.length ≤ P n := by
    simpa only [P, List.length_nil, Nat.add_zero] using (hbounds n []).2
  have hprf₀ := hprf.secure (cbcToPrfDistinguisher adversary false)
    (isOraclePPT_cbcToPrfDistinguisher hadversary false)
  have hprf₁ := hprf.secure (cbcToPrfDistinguisher adversary true)
    (isOraclePPT_cbcToPrfDistinguisher hadversary true)
  negligible using fun n => advantage_cbcWordCPAGame_prf_le hprf.length_eq adversary (hq n) (hl n)

/-- **Random-IV CBC mode is CPA-secure for a pseudorandom permutation** ([BonehShoup2023],
Section 5.4.3, Theorem 5.4, printed pp. 195–199): if `E` is a `BlockCipher` with `keyLen = id`,
`blockLen = id` and `E.PRP`, random-IV CBC mode with `n`-bit keys and `n`-bit blocks at security
parameter `n` has negligible many-query left-or-right CPA advantage on equal-length pairs of whole
blocks, against every uniform strict oracle-PPT adversary. See the module's deviations for the
unbounded whole-block message space and uniform adversary conventions. -/
theorem BlockCipher.PRP.indcpa_cbcWordEncrypt {E : BlockCipher} (hkey : E.keyLen = id)
    (hblock : E.blockLen = id) (hprp : E.PRP) :
    SymmetricINDCPAOn blockPairValid BitString.sampleList
      (cbcWordEncrypt fun k x => E.encrypt k.length k x) :=
  (hprp.pseudorandomFunction hkey hblock).indcpa_cbcWordEncrypt

end Cslib.Crypto
