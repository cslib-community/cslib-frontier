/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Probability.BitString.Collision
public import CslibFrontier.Probability.IID
public import Mathlib.Data.Fintype.Perm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Symmetric block-cipher modes of operation, collision lemmas, and mode separations

Block-cipher and pseudorandom-function modes of operation ([KatzLindell2020], Sections 3.6.2–3.6.4)
lift a fixed-width block function `f : BitString n → BitString n` (or permutation
`π : Equiv.Perm (BitString n)`) to multi-block messages using an initialization vector
`iv : BitString n`. Throughout this module, `BitString n` is equipped with Mathlib's coordinatewise
XOR group structure (`+` via `BooleanRing Bool`, where every element is its own inverse,
`BitString.add_self`). Cipher Feedback (CFB) mode is included alongside CBC, OFB, and CTR as a
standard self-synchronizing feedback mode (not covered in [KatzLindell2020]).

## Main definitions

* `cbcEncryptBlocks`, `cbcDecryptBlocks`: Cipher Block Chaining (CBC) encryption and decryption
  ([KatzLindell2020], Section 3.6.3, Figure 3.6).
* `ofbChain`, `ofbEncryptBlocks`, `ofbDecryptBlocks`: Output Feedback (OFB) keystream chain and
  encryption/decryption ([KatzLindell2020], Section 3.6.3, Figure 3.8).
* `cfbEncryptBlocks`, `cfbDecryptBlocks`: Cipher Feedback (CFB) encryption and decryption.
* `ctrMaskBlocks`, `ctrEncryptBlocks`, `ctrDecryptBlocks`: Counter (CTR) mode mask generation and
  encryption/decryption ([KatzLindell2020], Section 3.6.3, Figure 3.9).
* `goodChain`, `uniformBlocks`: collision-free step invariant and lazy-sampling block draws for
  multi-block feedback chains.
* `streamIVReuseTest`, `streamIVReuseRealGame`, `streamIVReuseIdealGame`: same-IV keystream
  cancellation distinguisher ([KatzLindell2020], Section 3.6.4).
* `overlappingStreamBlocks`, `overlappingStreamTest`, `overlappingStreamRealGame`,
  `overlappingStreamIdealGame`: overlapping counter/stream window distinguisher
  ([KatzLindell2020], Exercises 3.24 and 3.32).
* `cbcPredictableIVQuery`, `cbcPredictableIVGame`: predictable-IV chosen-plaintext attack on CBC
  mode ([KatzLindell2020], Section 3.6.3 and Exercise 3.33).
* `cfbSameIVRecover`, `xorFunctionCipher`, `xorFunctionCipherRecover`, `additiveModeCipher`,
  `additiveModeDistinguisher`: message-recovery and distinguishing attacks on reused-IV CFB,
  linear XOR encryption ([KatzLindell2020], Exercise 3.21), and additive-IV permutation mode over
  any commutative group ([KatzLindell2020], Exercise 3.25).
* `flipCipherBlockBit`, `dropCipherBlock`, `cbcBlockDecrypt`, `cfbBlockDecrypt`,
  `maskBlockDecrypt`, `ofbBlockMask`, `ctrBlockMask`: indexed block-stream decryption and
  transmission-error operators ([KatzLindell2020], Section 3.6.3, Exercises 3.29 and 3.30).

## Main results

* `cbcDecryptBlocks_cbcEncryptBlocks`, `ofbDecryptBlocks_ofbEncryptBlocks`,
  `cfbDecryptBlocks_cfbEncryptBlocks`, `ctrDecryptBlocks_ctrEncryptBlocks`: round-trip inversion
  identities, plus `ofbChain_eq_cbcEncryptBlocks_replicate_zero`.
* `advantage_xorEvalPoints_eq_zero`: masking with a uniform random function on any fixed
  (non-adaptive) injective point schedule `pts : ι → BitString n` (such as non-overlapping CTR
  counters) has zero distinguishing advantage, from the bit-string uniformity lemma
  `BitString.map_xorEvalPoints_uniformOfFintype`.
* `toOuterMeasure_badChain_le`: lazy-sampling chain collision bound
  `(bs.length * ks.length + bs.length.choose 2) / 2 ^ n`, built from the per-step bound
  `BitString.toOuterMeasure_addRight_mem_list_le`, used as a proof ingredient when analyzing
  random-IV chaining ([KatzLindell2020], Section 3.6.3).
* `ofbEncryptBlocks_zipWith_add_same_iv`, `ctrEncryptBlocks_zipWith_add_same_iv`,
  `advantage_streamIVReuseGame_eq`, `ctrEncryptBlocks_overlapping_nonce`,
  `advantage_overlappingStreamGame_eq`, `advantage_cbcPredictableIVGame_eq_one`,
  `cfbSameIVRecover_cfbEncryptBlocks`, `xorFunctionCipherRecover_correct`,
  `additiveModeDistinguisher_spec`: mode counterexamples and IV/nonce misuse separations.
* `maskBlockDecrypt_ofbBlockMask_ofbEncryptBlocks`,
  `maskBlockDecrypt_ctrBlockMask_ctrEncryptBlocks`: the indexed OFB / CTR masks decrypt the
  list-mode ciphertexts.
* `maskBlockDecrypt_flipBit`, `cbcBlockDecrypt_flipBit`, `cfbBlockDecrypt_flipBit`,
  `cbcBlockDecrypt_dropBlock`, `cfbBlockDecrypt_dropBlock`, `maskBlockDecrypt_dropBlock`:
  single-bit flip and dropped-block error-propagation laws.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Sections 3.6.2–3.6.4 and Exercises 3.21, 3.24, 3.25, 3.29, 3.30, 3.32, 3.33.
-/
@[expose] public section
namespace Cslib.Crypto
open Probability
open scoped ENNReal NNReal
variable {n : ℕ}
/-! ### Multi-block modes of operation (CBC, OFB, CFB, CTR) -/
/-- **Cipher Block Chaining (CBC) encryption** ([KatzLindell2020], Section 3.6.3, Figure 3.6):
  given block function `f : BitString n → BitString n`, chaining value `iv : BitString n`, and
  plaintext blocks `ms : List (BitString n)`, emits `c₁ = f (iv + m₁)` and continues from `c₁`. -/
def cbcEncryptBlocks (f : BitString n → BitString n) :
    BitString n → List (BitString n) → List (BitString n)
  | _, [] => []
  | iv, m :: ms =>
    let c := f (iv + m)
    c :: cbcEncryptBlocks f c ms
/-- **Cipher Block Chaining (CBC) decryption** ([KatzLindell2020], Section 3.6.3, Figure 3.6):
  given inverse block function `fInv : BitString n → BitString n`, chaining value
  `iv : BitString n`, and ciphertext blocks `cs : List (BitString n)`, recovers `m₁ = iv + fInv c₁`
  and continues from `c₁`. -/
def cbcDecryptBlocks (fInv : BitString n → BitString n) :
    BitString n → List (BitString n) → List (BitString n)
  | _, [] => []
  | iv, c :: cs => (iv + fInv c) :: cbcDecryptBlocks fInv c cs
/-- CBC encryption of the empty block list is empty. -/
@[simp]
theorem cbcEncryptBlocks_nil (f : BitString n → BitString n) (iv : BitString n) :
    cbcEncryptBlocks f iv [] = [] := rfl
/-- CBC encryption unfolds by encrypting `iv + m` and chaining from `f (iv + m)`. -/
@[simp]
theorem cbcEncryptBlocks_cons (f : BitString n → BitString n) (iv m : BitString n)
    (ms : List (BitString n)) :
    cbcEncryptBlocks f iv (m :: ms) = f (iv + m) :: cbcEncryptBlocks f (f (iv + m)) ms := rfl
/-- CBC decryption of the empty block list is empty. -/
@[simp]
theorem cbcDecryptBlocks_nil (fInv : BitString n → BitString n) (iv : BitString n) :
    cbcDecryptBlocks fInv iv [] = [] := rfl
/-- CBC decryption unfolds by recovering `iv + fInv c` and chaining from `c`. -/
@[simp]
theorem cbcDecryptBlocks_cons (fInv : BitString n → BitString n) (iv c : BitString n)
    (cs : List (BitString n)) :
    cbcDecryptBlocks fInv iv (c :: cs) = (iv + fInv c) :: cbcDecryptBlocks fInv c cs := rfl
/-- CBC encryption preserves the number of blocks. -/
@[simp]
theorem length_cbcEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) :
    (cbcEncryptBlocks f iv ms).length = ms.length := by
  induction ms generalizing iv with
  | nil => rfl
  | cons m ms ih => simp [ih]
/-- CBC decryption preserves the number of blocks. -/
@[simp]
theorem length_cbcDecryptBlocks (fInv : BitString n → BitString n) (iv : BitString n)
    (cs : List (BitString n)) :
    (cbcDecryptBlocks fInv iv cs).length = cs.length := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih => simp [ih]
/-- CBC decryption inverts CBC encryption whenever `fInv` is a left inverse of `f`. -/
theorem cbcDecryptBlocks_cbcEncryptBlocks {f fInv : BitString n → BitString n}
    (hInv : Function.LeftInverse fInv f) (iv : BitString n) (ms : List (BitString n)) :
    cbcDecryptBlocks fInv iv (cbcEncryptBlocks f iv ms) = ms := by
  induction ms generalizing iv with
  | nil => rfl
  | cons m ms ih => simp [hInv (iv + m), ih]
/-- CBC encryption inverts CBC decryption whenever `fInv` is a right inverse of `f`. -/
theorem cbcEncryptBlocks_cbcDecryptBlocks {f fInv : BitString n → BitString n}
    (hInv : Function.RightInverse fInv f) (iv : BitString n) (cs : List (BitString n)) :
    cbcEncryptBlocks f iv (cbcDecryptBlocks fInv iv cs) = cs := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih => simp [hInv c, ih]
/-- For a permutation `π : Equiv.Perm (BitString n)`, CBC decryption with `π.symm` inverts CBC
  encryption with `π`. -/
@[simp]
theorem cbcDecryptBlocks_cbcEncryptBlocks_perm (π : Equiv.Perm (BitString n)) (iv : BitString n)
    (ms : List (BitString n)) :
    cbcDecryptBlocks π.symm iv (cbcEncryptBlocks π iv ms) = ms :=
  cbcDecryptBlocks_cbcEncryptBlocks π.left_inv iv ms
/-- **Output Feedback (OFB) keystream chain** ([KatzLindell2020], Section 3.6.3, Figure 3.8): `k`
  iterations of `yᵢ = f yᵢ₋₁` starting from `y₀ = iv`. -/
def ofbChain (f : BitString n → BitString n) : BitString n → ℕ → List (BitString n)
  | _, 0 => []
  | iv, k + 1 => f iv :: ofbChain f (f iv) k
/-- **Output Feedback (OFB) encryption** ([KatzLindell2020], Section 3.6.3, Figure 3.8): XORs each
  plaintext block with the corresponding block of `ofbChain f iv ms.length`. -/
def ofbEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) : List (BitString n) :=
  List.zipWith (· + ·) (ofbChain f iv ms.length) ms
/-- **Output Feedback (OFB) decryption** is identical to `ofbEncryptBlocks`. -/
abbrev ofbDecryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (cs : List (BitString n)) : List (BitString n) :=
  ofbEncryptBlocks f iv cs
/-- `ofbChain f iv k` has length `k`. -/
@[simp]
theorem length_ofbChain (f : BitString n → BitString n) (iv : BitString n) (k : ℕ) :
    (ofbChain f iv k).length = k := by
  induction k generalizing iv with
  | zero => rfl
  | succ k ih => simp [ofbChain, ih]
/-- OFB encryption preserves the number of blocks. -/
@[simp]
theorem length_ofbEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) :
    (ofbEncryptBlocks f iv ms).length = ms.length := by
  simp [ofbEncryptBlocks]
private theorem zipWith_add_cancel_left :
    ∀ (ks ms : List (BitString n)), ks.length = ms.length →
      List.zipWith (· + ·) ks (List.zipWith (· + ·) ks ms) = ms
  | [], [], _ => rfl
  | k :: ks, m :: ms, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zipWith_add_cancel_left ks ms h]
/-- OFB decryption inverts OFB encryption for every block function `f`, without requiring `f` to
  be invertible. -/
@[simp]
theorem ofbDecryptBlocks_ofbEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) :
    ofbDecryptBlocks f iv (ofbEncryptBlocks f iv ms) = ms := by
  simp only [ofbDecryptBlocks, ofbEncryptBlocks, List.length_zipWith, length_ofbChain, min_self]
  exact zipWith_add_cancel_left (ofbChain f iv ms.length) ms (length_ofbChain f iv ms.length)
/-- **Structural equivalence between OFB and zero-block CBC**: the `k`-block OFB keystream chain
  equals the CBC encryption of `k` all-zero blocks. -/
theorem ofbChain_eq_cbcEncryptBlocks_replicate_zero (f : BitString n → BitString n)
    (iv : BitString n) (k : ℕ) :
    ofbChain f iv k = cbcEncryptBlocks f iv (List.replicate k 0) := by
  induction k generalizing iv with
  | zero => rfl
  | succ k ih => simp [ofbChain, List.replicate_succ, ih]
/-- **Cipher Feedback (CFB) encryption**: emits `c₁ = f iv +
  m₁` and feeds the ciphertext block `c₁` into the next block-function call. -/
def cfbEncryptBlocks (f : BitString n → BitString n) :
    BitString n → List (BitString n) → List (BitString n)
  | _, [] => []
  | iv, m :: ms =>
    let c := f iv + m
    c :: cfbEncryptBlocks f c ms
/-- **Cipher Feedback (CFB) decryption**: recovers `m₁ = f iv
  + c₁` and feeds `c₁` into the next block-function call, using only forward evaluations of `f`. -/
def cfbDecryptBlocks (f : BitString n → BitString n) :
    BitString n → List (BitString n) → List (BitString n)
  | _, [] => []
  | iv, c :: cs => (f iv + c) :: cfbDecryptBlocks f c cs
/-- CFB encryption of the empty block list is empty. -/
@[simp]
theorem cfbEncryptBlocks_nil (f : BitString n → BitString n) (iv : BitString n) :
    cfbEncryptBlocks f iv [] = [] := rfl
/-- CFB encryption unfolds by emitting `f iv + m` and chaining from `f iv + m`. -/
@[simp]
theorem cfbEncryptBlocks_cons (f : BitString n → BitString n) (iv m : BitString n)
    (ms : List (BitString n)) :
    cfbEncryptBlocks f iv (m :: ms) = (f iv + m) :: cfbEncryptBlocks f (f iv + m) ms := rfl
/-- CFB decryption of the empty block list is empty. -/
@[simp]
theorem cfbDecryptBlocks_nil (f : BitString n → BitString n) (iv : BitString n) :
    cfbDecryptBlocks f iv [] = [] := rfl
/-- CFB decryption unfolds by recovering `f iv + c` and chaining from `c`. -/
@[simp]
theorem cfbDecryptBlocks_cons (f : BitString n → BitString n) (iv c : BitString n)
    (cs : List (BitString n)) :
    cfbDecryptBlocks f iv (c :: cs) = (f iv + c) :: cfbDecryptBlocks f c cs := rfl
/-- CFB encryption preserves the number of blocks. -/
@[simp]
theorem length_cfbEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) :
    (cfbEncryptBlocks f iv ms).length = ms.length := by
  induction ms generalizing iv with
  | nil => rfl
  | cons m ms ih => simp [ih]
/-- CFB decryption preserves the number of blocks. -/
@[simp]
theorem length_cfbDecryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (cs : List (BitString n)) :
    (cfbDecryptBlocks f iv cs).length = cs.length := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih => simp [ih]
/-- CFB decryption inverts CFB encryption for every block function `f`, without requiring `f` to
  be invertible. -/
@[simp]
theorem cfbDecryptBlocks_cfbEncryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (ms : List (BitString n)) :
    cfbDecryptBlocks f iv (cfbEncryptBlocks f iv ms) = ms := by
  induction ms generalizing iv with
  | nil => rfl
  | cons m ms ih => simp [ih]
/-- CFB encryption inverts CFB decryption for every block function `f`. -/
@[simp]
theorem cfbEncryptBlocks_cfbDecryptBlocks (f : BitString n → BitString n) (iv : BitString n)
    (cs : List (BitString n)) :
    cfbEncryptBlocks f iv (cfbDecryptBlocks f iv cs) = cs := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih => simp [ih]
/-- **Counter (CTR) mode keystream blocks** ([KatzLindell2020], Section 3.6.3, Figure 3.9):
  evaluates `f (counter iv i)` for `i = 0, …, k - 1`. -/
def ctrMaskBlocks (f : BitString n → BitString n) (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (k : ℕ) : List (BitString n) :=
  (List.range k).map (fun i => f (counter iv i))
/-- **Counter (CTR) mode encryption** ([KatzLindell2020], Section 3.6.3, Figure 3.9): XORs each
  plaintext block with the corresponding counter mask block. -/
def ctrEncryptBlocks (f : BitString n → BitString n) (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (ms : List (BitString n)) : List (BitString n) :=
  List.zipWith (· + ·) (ctrMaskBlocks f counter iv ms.length) ms
/-- **Counter (CTR) mode decryption** is identical to `ctrEncryptBlocks`. -/
abbrev ctrDecryptBlocks (f : BitString n → BitString n) (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (cs : List (BitString n)) : List (BitString n) :=
  ctrEncryptBlocks f counter iv cs
/-- `ctrMaskBlocks f counter iv k` has length `k`. -/
@[simp]
theorem length_ctrMaskBlocks (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (k : ℕ) :
    (ctrMaskBlocks f counter iv k).length = k := by
  simp [ctrMaskBlocks]
/-- CTR encryption preserves the number of blocks. -/
@[simp]
theorem length_ctrEncryptBlocks (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (ms : List (BitString n)) :
    (ctrEncryptBlocks f counter iv ms).length = ms.length := by
  simp [ctrEncryptBlocks]
/-- CTR decryption inverts CTR encryption for every block function `f` and counter schedule
  `counter`, without requiring `f` to be invertible. -/
@[simp]
theorem ctrDecryptBlocks_ctrEncryptBlocks (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (ms : List (BitString n)) :
    ctrDecryptBlocks f counter iv (ctrEncryptBlocks f counter iv ms) = ms := by
  simp only [ctrDecryptBlocks, ctrEncryptBlocks, List.length_zipWith, length_ctrMaskBlocks,
    min_self]
  exact zipWith_add_cancel_left (ctrMaskBlocks f counter iv ms.length) ms
    (length_ctrMaskBlocks f counter iv ms.length)
/-! ### Random-function keystream uniformity and lazy-sampling chain collisions -/
/-- **Zero distinguishing advantage under distinct evaluation points**: for any injective point
  schedule `pts : ι → BitString n`, any two multi-block messages `m₀, m₁ : ι → BitString n`, and
  any distinguisher `D : (ι → BitString n) → Game`, the distinguishing advantage between
  masking `m₀` and masking `m₁` at `pts` under a uniform random function is `0`. -/
theorem advantage_xorEvalPoints_eq_zero {ι : Type*} [Finite ι]
    {pts : ι → BitString n} (hpts : Function.Injective pts) (m₀ m₁ : ι → BitString n)
    (D : (ι → BitString n) → Game) :
    Game.advantage
      (((PMF.uniformOfFintype (BitString n → BitString n)).map
        (fun g i => g (pts i) + m₀ i)).bind D)
      (((PMF.uniformOfFintype (BitString n → BitString n)).map
        (fun g i => g (pts i) + m₁ i)).bind D) = 0 := by
  cases nonempty_fintype ι
  classical
  rw [BitString.map_xorEvalPoints_uniformOfFintype hpts m₀,
    BitString.map_xorEvalPoints_uniformOfFintype hpts m₁,
    Game.advantage_self]
/-- **Good (collision-free) step invariant for lazy-sampled chains** (used in the style of the
  random-IV chaining analysis in [KatzLindell2020], Section 3.6.3): given a list
  `ks : List (BitString n)` of already-queried block-function inputs, current chaining block
  `c : BitString n`, remaining message blocks `bs : List (BitString n)` (arbitrary for CBC, or
  all-zero for OFB), and fresh uniform block draws `draws : List (BitString n)`, asserts that every
  step input `c + b` is fresh (not in `ks` or any earlier step of the chain). -/
def goodChain : List (BitString n) → BitString n → List (BitString n) → List (BitString n) → Prop
  | _, _, [], _ => True
  | ks, c, b :: bs, u :: us => (c + b) ∉ ks ∧ goodChain ((c + b) :: ks) u bs us
  | ks, c, b :: bs, [] => (c + b) ∉ ks ∧ goodChain ((c + b) :: ks) 0 bs []
/-- Distribution of `k` independent uniform `n`-bit blocks as a list, used to lazily sample an
  idealized chain of length `k`: the independent draws `PMF.iid` read off by `List.ofFn`. -/
noncomputable def uniformBlocks (k : ℕ) : PMF (List (BitString n)) :=
  (PMF.iid (PMF.uniformOfFintype (BitString n)) k).map List.ofFn
/-- No uniform blocks: the empty list. -/
@[simp]
theorem uniformBlocks_zero : uniformBlocks (n := n) 0 = PMF.pure [] := by
  simp [uniformBlocks, PMF.iid]
/-- `k + 1` uniform blocks: a uniform head followed by `k` independent uniform blocks. -/
theorem uniformBlocks_succ (k : ℕ) :
    uniformBlocks (n := n) (k + 1) =
      (PMF.uniformOfFintype (BitString n)).bind fun u => (uniformBlocks k).map (u :: ·) := by
  simp only [uniformBlocks, PMF.iid, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- Reading `k` independent uniform `n`-bit blocks as a function on `Fin k` and converting via
  `List.ofFn` equals `uniformBlocks k`. -/
theorem uniformBlocks_eq (k : ℕ) :
    uniformBlocks (n := n) k = (PMF.uniformOfFintype (Fin k → BitString n)).map List.ofFn := by
  rw [uniformBlocks, PMF.iid_uniformOfFintype]

/-- Every list in the support of `uniformBlocks k` has length `k`. -/
theorem length_of_mem_support_uniformBlocks {k : ℕ} {us : List (BitString n)}
    (h : us ∈ (uniformBlocks (n := n) k).support) : us.length = k := by
  obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact List.length_ofFn

/-- Every `(iv, us)` pair in the support of a uniform IV paired with `uniformBlocks k` has
  `us.length = k`. -/
theorem length_snd_of_mem_support_uniformDraws {k : ℕ}
    {p : BitString n × List (BitString n)}
    (h : p ∈ ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
      (uniformBlocks (n := n) k).map (iv, ·)).support) : p.2.length = k := by
  obtain ⟨iv, -, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
  obtain ⟨us, hus, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  exact length_of_mem_support_uniformBlocks hus

/-- XORing a fixed block sequence `ms` into `uniformBlocks ms.length` preserves the uniform
  distribution `uniformBlocks ms.length`. -/
theorem map_zipWith_uniformBlocks :
    ∀ ms : List (BitString n),
      (uniformBlocks ms.length).map (fun us => List.zipWith (· + ·) us ms) =
        uniformBlocks ms.length
  | [] => by simp
  | m :: ms => by
    calc (uniformBlocks (m :: ms).length).map (fun us => List.zipWith (· + ·) us (m :: ms))
        = (PMF.uniformOfFintype (BitString n)).bind fun u =>
            ((uniformBlocks ms.length).map fun us => List.zipWith (· + ·) us ms).map
              ((u + m) :: ·) := by
          simp only [List.length_cons, uniformBlocks_succ, PMF.map_bind, PMF.map_comp,
            Function.comp_def, List.zipWith_cons_cons]
      _ = (PMF.uniformOfFintype (BitString n)).bind fun u =>
            (uniformBlocks ms.length).map ((u + m) :: ·) := by
          rw [map_zipWith_uniformBlocks ms]
      _ = uniformBlocks (m :: ms).length := by
          rw [PMF.uniformOfFintype_bind_add_right m fun u => (uniformBlocks ms.length).map (u :: ·),
            List.length_cons, uniformBlocks_succ]

/-- XORing a fixed block sequence `ms` into the uniform block draws paired with an independent
  uniform IV leaves the joint `(iv, blocks)` distribution invariant. -/
theorem map_iv_uniformBlocks_zipWith (ms : List (BitString n)) :
    ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) ms.length).map (iv, ·)).map
      (fun p => (p.1, List.zipWith (· + ·) p.2 ms)) =
      (PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) ms.length).map (iv, ·) := by
  rw [PMF.map_bind]
  refine congrArg _ (funext fun iv => ?_)
  conv_rhs => rw [← map_zipWith_uniformBlocks ms]
  simp only [PMF.map_comp, Function.comp_def]

/-- **Lazy-sampled multi-block chain collision lemma**: when the initial chaining block `iv` and
  the `bs.length` step outputs are drawn independently and uniformly from `BitString n`, the outer
  measure of the bad event `¬goodChain ks iv bs draws` (some step input `cᵢ₋₁ + bᵢ` collides with
  `ks` or an earlier step input in the same chain) is at most
  `(bs.length * ks.length + bs.length.choose 2) / 2 ^ n`: the `j`-th step input meets one of the
  `ks.length + j` earlier inputs with probability at most `(ks.length + j) / 2 ^ n`. This bounds
  the bad-event probability in lazy random-function sampling in the style of [KatzLindell2020],
  Section 3.6.3. -/
theorem toOuterMeasure_badChain_le :
    ∀ (bs : List (BitString n)) (ks : List (BitString n)),
      ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) bs.length).map (iv, ·)).toOuterMeasure
        {p : BitString n × List (BitString n) | ¬goodChain ks p.1 bs p.2} ≤
      ((bs.length * ks.length + bs.length.choose 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹
  | [], ks => by simp [goodChain]
  | b :: bs, ks => by
    classical
    rw [List.length_cons]
    set C : ℝ≥0∞ :=
      ((bs.length * (ks.length + 1) + bs.length.choose 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹
    set S0 : Set (BitString n) := {iv | iv + b ∈ ks}
    refine le_trans (Probability.PMF.toOuterMeasure_bind_failure_le _ _ S0ᶜ _ C
      fun iv _ hiv => ?_) ?_
    · have hmap : (uniformBlocks (n := n) (bs.length + 1)).map (iv, ·) =
          ((PMF.uniformOfFintype (BitString n)).bind fun u =>
            (uniformBlocks (n := n) bs.length).map (u, ·)).map fun q => (iv, q.1 :: q.2) := by
        simp only [uniformBlocks_succ, PMF.map_bind, PMF.map_comp, Function.comp_def]
      have hiv' : iv + b ∉ ks := hiv
      rw [hmap, PMF.toOuterMeasure_map_apply]
      refine le_trans (MeasureTheory.measure_mono fun q => ?_)
        (by simpa only [C, List.length_cons] using toOuterMeasure_badChain_le bs ((iv + b) :: ks))
      simp [goodChain, hiv']
    · rw [compl_compl]
      calc (PMF.uniformOfFintype (BitString n)).toOuterMeasure S0 + C
          ≤ (ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ + C :=
            add_le_add (BitString.toOuterMeasure_addRight_mem_list_le ks b) le_rfl
        _ = ((bs.length + 1) * ks.length + (bs.length + 1).choose 2 : ℕ) *
              ((2 : ℝ≥0∞) ^ n)⁻¹ := by
            rw [Nat.choose_succ_succ' bs.length 1, Nat.choose_one_right]
            simp only [C, ← add_mul]
            congr 1
            push_cast
            ring
/-! ### IV-reuse, predictable-IV, and elementary encryption-mode counterexamples -/
private theorem zipWith_add_zipWith_add_same :
    ∀ (ks ms₀ ms₁ : List (BitString n)),
      ms₀.length ≤ ks.length → ms₁.length = ms₀.length →
      List.zipWith (· + ·) (List.zipWith (· + ·) ks ms₀) (List.zipWith (· + ·) ks ms₁) =
        List.zipWith (· + ·) ms₀ ms₁
  | _, [], [], _, _ => by simp
  | k :: ks, m₀ :: ms₀, m₁ :: ms₁, h₀, h₁ => by
    simp only [List.length_cons, Nat.add_le_add_iff_right, Nat.add_right_cancel_iff] at h₀ h₁
    simp only [List.zipWith_cons_cons, zipWith_add_zipWith_add_same ks ms₀ ms₁ h₀ h₁]
    rw [← add_assoc, add_right_comm k m₀ k, BitString.add_self, zero_add]
/-- **OFB IV-reuse keystream cancellation ([KatzLindell2020], Section 3.6.4)**: encrypting two
  equal-length block sequences `ms₀, ms₁` under the same `iv` in OFB mode cancels the keystream,
  leaking `List.zipWith (· + ·) ms₀ ms₁` for every block function `f`. -/
theorem ofbEncryptBlocks_zipWith_add_same_iv (f : BitString n → BitString n) (iv : BitString n)
    {ms₀ ms₁ : List (BitString n)} (hlen : ms₁.length = ms₀.length) :
    List.zipWith (· + ·) (ofbEncryptBlocks f iv ms₀) (ofbEncryptBlocks f iv ms₁) =
      List.zipWith (· + ·) ms₀ ms₁ := by
  rw [ofbEncryptBlocks, ofbEncryptBlocks, hlen]
  exact zipWith_add_zipWith_add_same (ofbChain f iv ms₀.length) ms₀ ms₁ (by simp) hlen
/-- **CTR IV-reuse keystream cancellation ([KatzLindell2020], Section 3.6.4)**: encrypting two
  equal-length block sequences `ms₀, ms₁` under the same `iv` in CTR mode cancels the keystream,
  leaking `List.zipWith (· + ·) ms₀ ms₁` for every block function `f` and counter schedule
  `counter`. -/
theorem ctrEncryptBlocks_zipWith_add_same_iv (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n)
    {ms₀ ms₁ : List (BitString n)} (hlen : ms₁.length = ms₀.length) :
    List.zipWith (· + ·) (ctrEncryptBlocks f counter iv ms₀) (ctrEncryptBlocks f counter iv ms₁) =
      List.zipWith (· + ·) ms₀ ms₁ := by
  rw [ctrEncryptBlocks, ctrEncryptBlocks, hlen]
  exact zipWith_add_zipWith_add_same (ctrMaskBlocks f counter iv ms₀.length) ms₀ ms₁ (by simp) hlen
/-- Two-ciphertext same-IV distinguisher for stream / OFB / CTR modes ([KatzLindell2020],
  Section 3.6.4): checks whether `c₀ + c₁ = m₀ + m₁`. -/
def streamIVReuseTest (m₀ m₁ : BitString n) (c : BitString n × BitString n) : Bool :=
  decide (c.1 + c.2 = m₀ + m₁)
/-- `streamIVReuseTest` accepts any pair of 1-block OFB ciphertexts encrypted under the same
  `iv`. -/
theorem streamIVReuseTest_ofbEncryptBlocks (f : BitString n → BitString n)
    (iv m₀ m₁ : BitString n) :
    streamIVReuseTest m₀ m₁
      ((ofbEncryptBlocks f iv [m₀]).getD 0 0, (ofbEncryptBlocks f iv [m₁]).getD 0 0) = true := by
  simp [streamIVReuseTest, ofbEncryptBlocks, ofbChain, ← add_assoc,
    add_right_comm (f iv) m₀ (f iv)]
/-- `streamIVReuseTest` accepts any pair of 1-block CTR ciphertexts encrypted under the same
  `iv`. -/
theorem streamIVReuseTest_ctrEncryptBlocks (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv m₀ m₁ : BitString n) :
    streamIVReuseTest m₀ m₁
      ((ctrEncryptBlocks f counter iv [m₀]).getD 0 0,
       (ctrEncryptBlocks f counter iv [m₁]).getD 0 0) = true := by
  simp [streamIVReuseTest, ctrEncryptBlocks, ctrMaskBlocks, ← add_assoc,
    add_right_comm (f (counter iv 0)) m₀ (f (counter iv 0))]
/-- Real same-IV stream-encryption game on two 1-block messages `m₀, m₁`: both blocks are masked
  by the same keystream block `pad`. -/
noncomputable def streamIVReuseRealGame (padDist : PMF (BitString n)) (m₀ m₁ : BitString n) :
    Game :=
  padDist.map fun pad => streamIVReuseTest m₀ m₁ (pad + m₀, pad + m₁)
/-- Ideal two-ciphertext game: the two ciphertext blocks are independent uniform `n`-bit blocks. -/
noncomputable def streamIVReuseIdealGame (m₀ m₁ : BitString n) : Game :=
  (PMF.uniformOfFintype (BitString n × BitString n)).map (streamIVReuseTest m₀ m₁)
/-- In the same-IV stream game, the keystream pad cancels and `streamIVReuseTest` always outputs
  `true`. -/
@[simp]
theorem streamIVReuseRealGame_eq_pure_true (padDist : PMF (BitString n)) (m₀ m₁ : BitString n) :
    streamIVReuseRealGame padDist m₀ m₁ = PMF.pure true := by
  have hcancel (pad : BitString n) : (pad + m₀) + (pad + m₁) = m₀ + m₁ := by
    rw [← add_assoc, add_right_comm pad m₀ pad, BitString.add_self, zero_add]
  simp only [streamIVReuseRealGame, streamIVReuseTest, hcancel, decide_true]
  exact PMF.map_const padDist true
private theorem uniform_addHom_decide_eq_apply_true {α : Type*} [Fintype α] [AddGroup α]
    (φ : α →+ BitString n) (hsurj : Function.Surjective φ) (target : BitString n) :
    (PMF.uniformOfFintype α).map (fun x => decide (φ x = target)) true = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [← Function.comp_def (fun s => decide (s = target)) φ, ← PMF.map_comp,
    PMF.uniformOfFintype_map_addHom φ hsurj, PMF.map_apply, tsum_fintype]
  simp [PMF.uniformOfFintype_apply, eq_comm (a := true)]

private theorem advantage_pure_true_of_apply_true_inv_two_pow {g₁ g₂ : Game}
    (h₁ : g₁ = PMF.pure true) (h₂ : g₂ true = ((2 : ℝ≥0∞) ^ n)⁻¹) :
    Game.advantage g₁ g₂ = 1 - ((2 : ℝ≥0) ^ n)⁻¹ := by
  ext
  have hle : ((2 : ℝ≥0) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  rw [h₁, Game.coe_advantage_pure_true_left, h₂, NNReal.coe_sub hle]
  simp

/-- On two independent uniform `n`-bit ciphertext blocks, `streamIVReuseTest` accepts with exact
  probability `(2 ^ n)⁻¹`. -/
theorem streamIVReuseIdealGame_apply_true (m₀ m₁ : BitString n) :
    streamIVReuseIdealGame m₀ m₁ true = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  let φ : BitString n × BitString n →+ BitString n :=
    { toFun := fun c => c.1 + c.2
      map_zero' := by simp
      map_add' := fun a b => by simp [add_left_comm, add_comm] }
  exact uniform_addHom_decide_eq_apply_true φ (fun y => ⟨(y, 0), by simp [φ]⟩) (m₀ + m₁)
/-- **Exact advantage of the same-IV distinguisher ([KatzLindell2020], Section 3.6.4)**: reusing
  an IV on two messages gives distinguishing advantage `1 - (2 ^ n)⁻¹` against uniform
  ciphertexts for every pad distribution `padDist`. -/
theorem advantage_streamIVReuseGame_eq (padDist : PMF (BitString n)) (m₀ m₁ : BitString n) :
    Game.advantage (streamIVReuseRealGame padDist m₀ m₁) (streamIVReuseIdealGame m₀ m₁) =
      1 - ((2 : ℝ≥0) ^ n)⁻¹ :=
  advantage_pure_true_of_apply_true_inv_two_pow
    (streamIVReuseRealGame_eq_pure_true padDist m₀ m₁) (streamIVReuseIdealGame_apply_true m₀ m₁)
/-- **Overlapping stream / nonce-CTR keystream blocks ([KatzLindell2020], Exercises 3.24 and
  3.32)**: generating two 2-block keystreams from distinct nonces `iv` and `step iv` produces
  `((f (step iv), f (step (step iv))), (f (step (step iv)), f (step (step (step iv)))))`, whose
  inner blocks always coincide because the counter windows overlap at `step (step iv)`. -/
def overlappingStreamBlocks (f step : BitString n → BitString n) (iv : BitString n) :
    (BitString n × BitString n) × (BitString n × BitString n) :=
  ((f (step iv), f (step (step iv))), (f (step (step iv)), f (step (step (step iv)))))
/-- **Overlapping-counter nonce-CTR keystream recovery ([KatzLindell2020], Exercise 3.32)**:
  for the step-based counter schedule `ctr v i = (step^[i + 1]) v`, encrypting two 2-block
  plaintexts `[m₀, m₁]` and `[m₀', m₁']` under nonces `iv` and `step iv` and XORing out the
  known plaintexts yields `overlappingStreamBlocks f step iv`. -/
theorem ctrEncryptBlocks_overlapping_nonce (f step : BitString n → BitString n)
    (iv m₀ m₁ m₀' m₁' : BitString n) :
    let ctr := fun v (i : ℕ) => (step^[i + 1]) v
    let c₁ := ctrEncryptBlocks f ctr iv [m₀, m₁]
    let c₂ := ctrEncryptBlocks f ctr (step iv) [m₀', m₁']
    ((c₁.getD 0 0 + m₀, c₁.getD 1 0 + m₁),
     (c₂.getD 0 0 + m₀', c₂.getD 1 0 + m₁')) =
      overlappingStreamBlocks f step iv := by
  simp [ctrEncryptBlocks, ctrMaskBlocks, List.range_succ, overlappingStreamBlocks]
/-- Distinguisher for Exercises 3.24 and 3.32: checks whether the second block of the first output
  equals the first block of the second output. -/
def overlappingStreamTest : (BitString n × BitString n) × (BitString n × BitString n) → Bool :=
  fun ((_, inner₁), (inner₂, _)) => decide (inner₁ = inner₂)
/-- `overlappingStreamTest` always accepts `overlappingStreamBlocks f step iv`. -/
@[simp]
theorem overlappingStreamTest_overlappingStreamBlocks (f step : BitString n → BitString n)
    (iv : BitString n) :
    overlappingStreamTest (overlappingStreamBlocks f step iv) = true := by
  simp [overlappingStreamTest, overlappingStreamBlocks]
/-- Real experiment for Exercises 3.24 and 3.32 over any initial nonce/IV distribution `ivDist`. -/
noncomputable def overlappingStreamRealGame (f step : BitString n → BitString n)
    (ivDist : PMF (BitString n)) : Game :=
  ivDist.map fun iv => overlappingStreamTest (overlappingStreamBlocks f step iv)
/-- Ideal experiment for Exercises 3.24 and 3.32: four independent uniform `n`-bit blocks. -/
noncomputable def overlappingStreamIdealGame (n : ℕ) : Game :=
  (PMF.uniformOfFintype ((BitString n × BitString n) × (BitString n × BitString n))).map
    overlappingStreamTest
/-- In the real overlapping-stream experiment, `overlappingStreamTest` accepts with probability
  `1`. -/
@[simp]
theorem overlappingStreamRealGame_eq_pure_true (f step : BitString n → BitString n)
    (ivDist : PMF (BitString n)) :
    overlappingStreamRealGame f step ivDist = PMF.pure true := by
  simp only [overlappingStreamRealGame, overlappingStreamTest_overlappingStreamBlocks]
  exact PMF.map_const ivDist true
/-- On four independent uniform `n`-bit blocks, `overlappingStreamTest` accepts with exact
  probability `(2 ^ n)⁻¹`. -/
theorem overlappingStreamIdealGame_apply_true (n : ℕ) :
    overlappingStreamIdealGame n true = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  let φ : (BitString n × BitString n) × (BitString n × BitString n) →+ BitString n :=
    { toFun := fun out => out.1.2 + out.2.1
      map_zero' := by simp
      map_add' := fun a b => by simp [add_left_comm, add_comm] }
  have htest : overlappingStreamTest (n := n) = fun out => decide (φ out = 0) := by
    funext ⟨⟨_, _⟩, ⟨_, _⟩⟩
    simp [overlappingStreamTest, φ, funext_iff, BooleanRing.add_eq_zero']
  rw [overlappingStreamIdealGame, htest]
  exact uniform_addHom_decide_eq_apply_true φ (fun y => ⟨((0, y), (0, 0)), by simp [φ]⟩) 0
/-- **Exact advantage for overlapping counter/stream nonces ([KatzLindell2020], Exercises 3.24 and
  3.32)**: `overlappingStreamTest` distinguishes `overlappingStreamBlocks` (under distinct nonces
  `iv` and `step iv`) from four uniform `n`-bit blocks with exact advantage `1 - (2 ^ n)⁻¹`. -/
theorem advantage_overlappingStreamGame_eq (f step : BitString n → BitString n)
    (ivDist : PMF (BitString n)) :
    Game.advantage (overlappingStreamRealGame f step ivDist) (overlappingStreamIdealGame n) =
      1 - ((2 : ℝ≥0) ^ n)⁻¹ :=
  advantage_pure_true_of_apply_true_inv_two_pow
    (overlappingStreamRealGame_eq_pure_true f step ivDist) (overlappingStreamIdealGame_apply_true n)
/-- **Predictable-IV CBC CPA query ([KatzLindell2020], Section 3.6.3 and Exercise 3.33)**: if the
  first encryption query uses `iv₁` and the challenge encryption uses a predictable `iv₂`,
  querying `cbcPredictableIVQuery iv₁ iv₂ m₀ = iv₁ + iv₂ + m₀` forces the first query's CBC block
  input to equal the challenge's CBC block input on `m₀`. -/
def cbcPredictableIVQuery (iv₁ iv₂ m₀ : BitString n) : BitString n :=
  iv₁ + iv₂ + m₀
/-- XORing `iv₁` with `cbcPredictableIVQuery iv₁ iv₂ m₀` produces the target CBC input `iv₂ +
  m₀`. -/
@[simp]
theorem add_cbcPredictableIVQuery (iv₁ iv₂ m₀ : BitString n) :
    iv₁ + cbcPredictableIVQuery iv₁ iv₂ m₀ = iv₂ + m₀ := by
  simp [cbcPredictableIVQuery, ← add_assoc]
/-- Encrypting `cbcPredictableIVQuery iv₁ iv₂ m₀` under `iv₁` in CBC mode produces the same
  1-block ciphertext as encrypting `m₀` under `iv₂`. -/
theorem cbcEncryptBlocks_cbcPredictableIVQuery (f : BitString n → BitString n)
    (iv₁ iv₂ m₀ : BitString n) :
    cbcEncryptBlocks f iv₁ [cbcPredictableIVQuery iv₁ iv₂ m₀] = cbcEncryptBlocks f iv₂ [m₀] := by
  simp
/-- For any injective block function `f`, the predictable-IV CBC query matches the challenge
  ciphertext on `if b then m₁ else m₀` (`m₀ ≠ m₁`) if and only if `b = false`. -/
theorem cbcPredictableIV_eq_iff {f : BitString n → BitString n} (hf : Function.Injective f)
    (iv₁ iv₂ m₀ m₁ : BitString n) (hne : m₀ ≠ m₁) (b : Bool) :
    cbcEncryptBlocks f iv₁ [cbcPredictableIVQuery iv₁ iv₂ m₀] =
      cbcEncryptBlocks f iv₂ [if b then m₁ else m₀] ↔ b = false := by
  cases b <;> simp [hf.eq_iff, hne]
/-- Predictable-IV CBC CPA game for challenge bit `b`: the adversary queries
  `cbcPredictableIVQuery iv₁ iv₂ m₀` under `iv₁`, receives challenge ciphertext under `iv₂`, and
  tests whether the two ciphertext blocks are equal. -/
noncomputable def cbcPredictableIVGame (f : BitString n → BitString n) (iv₁ iv₂ m₀ m₁ : BitString n)
    (b : Bool) : Game :=
  PMF.pure (decide (cbcEncryptBlocks f iv₁ [cbcPredictableIVQuery iv₁ iv₂ m₀] =
    cbcEncryptBlocks f iv₂ [if b then m₁ else m₀]))
/-- **Predictable-IV CBC CPA break ([KatzLindell2020], Section 3.6.3 and Exercise 3.33)**: for
  any injective block function `f` and distinct messages `m₀ ≠ m₁`, the 1-query predictable-IV
  adversary distinguishes `b = false` from `b = true` with advantage `1`. -/
theorem advantage_cbcPredictableIVGame_eq_one {f : BitString n → BitString n}
    (hf : Function.Injective f) (iv₁ iv₂ m₀ m₁ : BitString n) (hne : m₀ ≠ m₁) :
    Game.advantage (cbcPredictableIVGame f iv₁ iv₂ m₀ m₁ false)
      (cbcPredictableIVGame f iv₁ iv₂ m₀ m₁ true) = 1 := by
  simp [cbcPredictableIVGame, Game.succProbability, hf.eq_iff, hne]
/-- **Same-IV CFB plaintext recovery**: if two CFB encryptions reuse the same `iv`, given known
  message block `m₁`, its first ciphertext block `c₁ = f iv + m₁`, and a target first ciphertext
  block `cStar = f iv + mStar`, XORing `c₁ + m₁ + cStar` recovers `mStar` exactly for every block
  function `f`. -/
def cfbSameIVRecover (m₁ c₁ cStar : BitString n) : BitString n :=
  c₁ + m₁ + cStar
/-- `cfbSameIVRecover` recovers the target first plaintext block `mStar` from a known-plaintext
  CFB encryption under the same `iv`. -/
@[simp]
theorem cfbSameIVRecover_cfbEncryptBlocks (f : BitString n → BitString n)
    (iv m₁ mStar : BitString n) :
    cfbSameIVRecover m₁ (f iv + m₁) (f iv + mStar) = mStar := by
  unfold cfbSameIVRecover
  rw [add_assoc (f iv) m₁ m₁, BitString.add_self, add_zero, BitString.add_cancel_left]
/-- **Linear XOR-keyed encryption ([KatzLindell2020], Exercise 3.21)**: encrypts `m` under key
  `k` and randomness `r` as `(r, k + r + m)`. -/
def xorFunctionCipher (k r m : BitString n) : BitString n × BitString n :=
  (r, k + r + m)
/-- One-query message recovery for `xorFunctionCipher`: from a single encryption `(r₁, c₁)` of
  `0` and a target ciphertext `(r₂, c₂)`, computes `r₁ + c₁ + r₂ + c₂ = m`. -/
def xorFunctionCipherRecover (q c : BitString n × BitString n) : BitString n :=
  q.1 + q.2 + c.1 + c.2
/-- `xorFunctionCipherRecover` recovers any message `m` from a single encryption of `0` under any
  randomness `r₁, r₂`. -/
@[simp]
theorem xorFunctionCipherRecover_correct (k r₁ r₂ m : BitString n) :
    xorFunctionCipherRecover (xorFunctionCipher k r₁ 0) (xorFunctionCipher k r₂ m) = m := by
  unfold xorFunctionCipherRecover xorFunctionCipher
  rw [add_zero, add_comm r₁ (k + r₁), add_assoc k r₁ r₁, BitString.add_self, add_zero,
    BitString.add_cancel_left]
/-- **Additive-IV two-block permutation mode ([KatzLindell2020], Exercise 3.25)**: over any block
  type `B` with addition `+` (such as `ZMod (2 ^ n)` for modular addition `mod 2^n`, or
  `BitString n` for XOR), given a block function `π : B → α` and step offset `δ : B` (e.g.
  `1 : ZMod (2 ^ n)`), encrypts `(m₁, m₂)` with random `r : B` as
  `(r, (π (r + m₁), π (r + δ + m₂)))`. -/
def additiveModeCipher {B α : Type*} [Add B] (π : B → α) (δ r m₁ m₂ : B) : B × (α × α) :=
  (r, (π (r + m₁), π (r + δ + m₂)))
/-- Zero-query distinguisher for `additiveModeCipher` on `M₀ = (0, 0)` vs `M₁ = (0, -δ)`: tests
  whether the two ciphertext blocks are equal (`c₁ = c₂`). -/
def additiveModeDistinguisher {B α : Type*} [DecidableEq α] : B × (α × α) → Bool :=
  fun (_, (c₁, c₂)) => decide (c₁ = c₂)
/-- For any injective `π : B → α` over `[AddCommGroup B]` and nonzero step `δ ≠ 0`,
  `additiveModeDistinguisher` rejects every encryption of `(0, 0)` and accepts every encryption of
  `(0, -δ)` ([KatzLindell2020], Exercise 3.25). -/
theorem additiveModeDistinguisher_spec {B α : Type*} [AddCommGroup B] [DecidableEq α]
    {π : B → α} (hπ : Function.Injective π) {δ : B} (hδ : δ ≠ 0) (r : B) :
    additiveModeDistinguisher (additiveModeCipher π δ r 0 0) = false ∧
      additiveModeDistinguisher (additiveModeCipher π δ r 0 (-δ)) = true := by
  exact ⟨by simp [additiveModeDistinguisher, additiveModeCipher, hπ.eq_iff, hδ],
    by simp [additiveModeDistinguisher, additiveModeCipher]⟩
/-! ### Transmission error-propagation laws and separations (Exercises 3.29 and 3.30) -/
/-- Flip bit `i : Fin n` of ciphertext block `b : ℕ` in an indexed block stream `c : ℕ →
  BitString n`. -/
def flipCipherBlockBit (c : ℕ → BitString n) (b : ℕ) (i : Fin n) : ℕ → BitString n :=
  fun j k => if j = b ∧ k = i then !(c j k) else c j k
/-- Drop ciphertext block `b : ℕ` from an indexed block stream `c : ℕ → BitString n`, shifting
  all blocks at index `≥ b` left by one position. -/
def dropCipherBlock (c : ℕ → BitString n) (b : ℕ) : ℕ → BitString n :=
  fun j => if j < b then c j else c (j + 1)
/-- Indexed-stream CBC decryption: block `0` is the IV (`c 0 = iv`), and plaintext block `j ≥ 1`
  is recovered as `c (j - 1) + fInv (c j)`. -/
def cbcBlockDecrypt (fInv : BitString n → BitString n) (c : ℕ → BitString n) (j : ℕ) :
    BitString n :=
  c (j - 1) + fInv (c j)
/-- Indexed-stream CFB decryption: block `0` is the IV (`c 0 = iv`), and plaintext block `j ≥ 1`
  is recovered as `f (c (j - 1)) + c j`. -/
def cfbBlockDecrypt (f : BitString n → BitString n) (c : ℕ → BitString n) (j : ℕ) :
    BitString n :=
  f (c (j - 1)) + c j
/-- Indexed-stream mask decryption (covering OFB and CTR modes): plaintext block `j ≥ 1` is `mask
  iv j + c j`. -/
def maskBlockDecrypt (mask : BitString n → ℕ → BitString n) (iv : BitString n)
    (c : ℕ → BitString n) (j : ℕ) : BitString n :=
  mask iv j + c j
/-- Indexed OFB block mask: `ofbBlockMask f iv j = f^[j] iv`. -/
def ofbBlockMask (f : BitString n → BitString n) (iv : BitString n) (j : ℕ) : BitString n :=
  (f^[j]) iv
/-- Indexed CTR block mask: `ctrBlockMask f counter iv j = f (counter iv (j - 1))`, so that
  indexed block `j ≥ 1` uses the same counter value as list block `j - 1` of `ctrMaskBlocks`. -/
def ctrBlockMask (f : BitString n → BitString n) (counter : BitString n → ℕ → BitString n)
    (iv : BitString n) (j : ℕ) : BitString n :=
  f (counter iv (j - 1))
/-- Indexed OFB decryption agrees with list OFB encryption: if the indexed stream `c` carries the
  list ciphertext `ofbEncryptBlocks f iv ms` at positions `1, …, ms.length`, then indexed block
  `j + 1` decrypts to plaintext block `j`. -/
theorem maskBlockDecrypt_ofbBlockMask_ofbEncryptBlocks (f : BitString n → BitString n)
    (iv : BitString n) (ms : List (BitString n)) (c : ℕ → BitString n)
    (hc : ∀ j (hj : j < ms.length), c (j + 1) = (ofbEncryptBlocks f iv ms)[j]'(by simpa)) :
    ∀ j (hj : j < ms.length), maskBlockDecrypt (ofbBlockMask f) iv c (j + 1) = ms[j] := by
  intro j hj
  have hchain (v : BitString n) (k : ℕ) : ∀ (i : ℕ) (hi : i < k),
      (ofbChain f v k)[i]'(by simpa) = (f^[i + 1]) v := by
    induction k generalizing v with
    | zero => omega
    | succ k ih =>
      rintro (_ | i) hi
      · simp [ofbChain]
      · simp [ofbChain, ih (f v) i (Nat.lt_of_succ_lt_succ hi), Function.iterate_succ_apply]
  simp only [maskBlockDecrypt, ofbBlockMask, hc j hj, ofbEncryptBlocks, List.getElem_zipWith]
  rw [hchain iv ms.length j hj, ← add_assoc, BitString.add_self, zero_add]
/-- Indexed CTR decryption agrees with list CTR encryption: if the indexed stream `c` carries the
  list ciphertext `ctrEncryptBlocks f counter iv ms` at positions `1, …, ms.length`, then indexed
  block `j + 1` decrypts to plaintext block `j`, for every counter schedule `counter`. -/
theorem maskBlockDecrypt_ctrBlockMask_ctrEncryptBlocks (f : BitString n → BitString n)
    (counter : BitString n → ℕ → BitString n) (iv : BitString n) (ms : List (BitString n))
    (c : ℕ → BitString n)
    (hc : ∀ j (hj : j < ms.length), c (j + 1) = (ctrEncryptBlocks f counter iv ms)[j]'(by simpa)) :
    ∀ j (hj : j < ms.length), maskBlockDecrypt (ctrBlockMask f counter) iv c (j + 1) = ms[j] := by
  intro j hj
  simp only [maskBlockDecrypt, ctrBlockMask, hc j hj, ctrEncryptBlocks, ctrMaskBlocks,
    List.getElem_zipWith, List.getElem_map, List.getElem_range, Nat.add_sub_cancel]
  rw [← add_assoc, BitString.add_self, zero_add]
private theorem flipCipherBlockBit_of_ne (c : ℕ → BitString n) {b j : ℕ} (i : Fin n) (h : j ≠ b) :
    flipCipherBlockBit c b i j = c j := by
  funext k; simp [flipCipherBlockBit, h]

private theorem add_flipCipherBlockBit_self (x : BitString n) (c : ℕ → BitString n) (b : ℕ)
    (i : Fin n) :
    (x + flipCipherBlockBit c b i b) i = !(x + c b) i ∧
      ∀ k : Fin n, k ≠ i → (x + flipCipherBlockBit c b i b) k = (x + c b) k := by
  refine ⟨?_, fun k hk => ?_⟩
  · change (x i ^^ flipCipherBlockBit c b i b i) = !(x i ^^ c b i)
    simp only [flipCipherBlockBit, and_self, ↓reduceIte]
    cases x i <;> cases c b i <;> rfl
  · change (x k ^^ flipCipherBlockBit c b i b k) = (x k ^^ c b k)
    simp [flipCipherBlockBit, hk]

/-- **OFB / CTR single-bit flip law ([KatzLindell2020], Exercise 3.29)**: flipping bit `i` of
  ciphertext block `b` flips only bit `i` of recovered plaintext block `b` and leaves every other
  block `j ≠ b` and every other bit `k ≠ i` unchanged. -/
theorem maskBlockDecrypt_flipBit (mask : BitString n → ℕ → BitString n) (iv : BitString n)
    (c : ℕ → BitString n) (b : ℕ) (i : Fin n) :
    maskBlockDecrypt mask iv (flipCipherBlockBit c b i) b i = !(maskBlockDecrypt mask iv c b i) ∧
      (∀ k : Fin n, k ≠ i →
        maskBlockDecrypt mask iv (flipCipherBlockBit c b i) b k = maskBlockDecrypt mask iv c b k) ∧
      (∀ j : ℕ, j ≠ b →
        maskBlockDecrypt mask iv (flipCipherBlockBit c b i) j = maskBlockDecrypt mask iv c j) := by
  obtain ⟨hflip, hother⟩ := add_flipCipherBlockBit_self (mask iv b) c b i
  exact ⟨hflip, hother, fun j hj => by simp [maskBlockDecrypt, flipCipherBlockBit_of_ne c i hj]⟩
/-- **OFB / CTR IV modification law ([KatzLindell2020], Exercise 3.29)**: replacing `iv` by `iv'`
  shifts every recovered plaintext block `j` by `mask iv' j + mask iv j`. -/
theorem maskBlockDecrypt_changeIV (mask : BitString n → ℕ → BitString n) (iv iv' : BitString n)
    (c : ℕ → BitString n) (j : ℕ) :
    maskBlockDecrypt mask iv' c j =
      maskBlockDecrypt mask iv c j + (mask iv' j + mask iv j) := by
  unfold maskBlockDecrypt
  rw [add_comm (mask iv' j) (mask iv j), ← add_assoc (mask iv j + c j),
    add_right_comm (mask iv j) (c j) (mask iv j), BitString.add_self, zero_add, add_comm]
/-- **CBC single-bit flip law ([KatzLindell2020], Exercise 3.29)**: flipping bit `i` of
  ciphertext block `b ≥ 1` replaces block `b` with `c (b - 1) + fInv (flipCipherBlockBit c b i
  b)`, flips bit `i` of block `b + 1` while keeping all other bits `k ≠ i` of block `b + 1`
  unchanged, and leaves every block `j ∉ {b, b + 1}` (`j ≥ 1`) completely unchanged. -/
theorem cbcBlockDecrypt_flipBit (fInv : BitString n → BitString n) (c : ℕ → BitString n)
    (b : ℕ) (hb : 1 ≤ b) (i : Fin n) :
    cbcBlockDecrypt fInv (flipCipherBlockBit c b i) b =
        c (b - 1) + fInv (flipCipherBlockBit c b i b) ∧
      cbcBlockDecrypt fInv (flipCipherBlockBit c b i) (b + 1) i =
        !(cbcBlockDecrypt fInv c (b + 1) i) ∧
      (∀ k : Fin n, k ≠ i →
        cbcBlockDecrypt fInv (flipCipherBlockBit c b i) (b + 1) k =
          cbcBlockDecrypt fInv c (b + 1) k) ∧
      (∀ j : ℕ, 1 ≤ j → j ≠ b → j ≠ b + 1 →
        cbcBlockDecrypt fInv (flipCipherBlockBit c b i) j = cbcBlockDecrypt fInv c j) := by
  have hnext := flipCipherBlockBit_of_ne c i (Nat.succ_ne_self b)
  obtain ⟨hflip, hother⟩ := add_flipCipherBlockBit_self (fInv (c (b + 1))) c b i
  refine ⟨by simp [cbcBlockDecrypt, flipCipherBlockBit_of_ne c i (Nat.sub_one_lt_of_lt hb).ne],
    by simpa only [cbcBlockDecrypt, Nat.add_sub_cancel, hnext, add_comm] using hflip,
    fun k hk =>
      by simpa only [cbcBlockDecrypt, Nat.add_sub_cancel, hnext, add_comm] using hother k hk,
    fun j hj hjb hjb1 => ?_⟩
  simp [cbcBlockDecrypt, flipCipherBlockBit_of_ne c i (mt (Nat.sub_eq_iff_eq_add hj).mp hjb1),
    flipCipherBlockBit_of_ne c i hjb]
/-- **CFB single-bit flip law**: flipping bit `i` of
  ciphertext block `b ≥ 1` flips only bit `i` of plaintext block `b`, replaces block `b + 1` with
  `f (flipCipherBlockBit c b i b) + c (b + 1)`, and leaves every block `j ∉ {b, b + 1}` (`j ≥ 1`)
  completely unchanged. -/
theorem cfbBlockDecrypt_flipBit (f : BitString n → BitString n) (c : ℕ → BitString n)
    (b : ℕ) (hb : 1 ≤ b) (i : Fin n) :
    cfbBlockDecrypt f (flipCipherBlockBit c b i) b i = !(cfbBlockDecrypt f c b i) ∧
      (∀ k : Fin n, k ≠ i →
        cfbBlockDecrypt f (flipCipherBlockBit c b i) b k = cfbBlockDecrypt f c b k) ∧
      cfbBlockDecrypt f (flipCipherBlockBit c b i) (b + 1) =
        f (flipCipherBlockBit c b i b) + c (b + 1) ∧
      (∀ j : ℕ, 1 ≤ j → j ≠ b → j ≠ b + 1 →
        cfbBlockDecrypt f (flipCipherBlockBit c b i) j = cfbBlockDecrypt f c j) := by
  have hprev := flipCipherBlockBit_of_ne c i (Nat.sub_one_lt_of_lt hb).ne
  obtain ⟨hflip, hother⟩ := add_flipCipherBlockBit_self (f (c (b - 1))) c b i
  refine ⟨by simpa only [cfbBlockDecrypt, hprev] using hflip,
    fun k hk => by simpa only [cfbBlockDecrypt, hprev] using hother k hk,
    by simp [cfbBlockDecrypt, flipCipherBlockBit_of_ne c i (Nat.succ_ne_self b)],
    fun j hj hjb hjb1 => ?_⟩
  simp [cfbBlockDecrypt, flipCipherBlockBit_of_ne c i (mt (Nat.sub_eq_iff_eq_add hj).mp hjb1),
    flipCipherBlockBit_of_ne c i hjb]

private theorem pairBlockDecrypt_dropBlock (g : BitString n → BitString n → BitString n)
    (c : ℕ → BitString n) {b : ℕ} (hb : 1 ≤ b) :
    (∀ j : ℕ, 1 ≤ j → j < b →
      g (dropCipherBlock c b (j - 1)) (dropCipherBlock c b j) = g (c (j - 1)) (c j)) ∧
      g (dropCipherBlock c b (b - 1)) (dropCipherBlock c b b) = g (c (b - 1)) (c (b + 1)) ∧
      (∀ j : ℕ, b < j →
        g (dropCipherBlock c b (j - 1)) (dropCipherBlock c b j) = g (c j) (c (j + 1))) := by
  refine ⟨fun j _ hjb => ?_, ?_, fun j hbj => ?_⟩
  · simp [dropCipherBlock, hjb, (Nat.sub_le j 1).trans_lt hjb]
  · simp [dropCipherBlock, Nat.sub_one_lt_of_lt hb]
  · simp [dropCipherBlock, not_lt.mpr (Nat.le_sub_one_of_lt hbj), not_lt.mpr hbj.le,
      Nat.sub_add_cancel (hb.trans hbj.le)]

/-- **CBC dropped-block resynchronization ([KatzLindell2020], Exercise 3.30)**: dropping
  ciphertext block `b ≥ 1` leaves blocks `1 ≤ j < b` unchanged, corrupts block `b` to `c (b - 1)
  + fInv (c (b + 1))`, and resynchronizes every subsequent block `j > b` to the shifted plaintext
  block `cbcBlockDecrypt fInv c (j + 1)`. -/
theorem cbcBlockDecrypt_dropBlock (fInv : BitString n → BitString n) (c : ℕ → BitString n)
    (b : ℕ) (hb : 1 ≤ b) :
    (∀ j : ℕ, 1 ≤ j → j < b →
      cbcBlockDecrypt fInv (dropCipherBlock c b) j = cbcBlockDecrypt fInv c j) ∧
      cbcBlockDecrypt fInv (dropCipherBlock c b) b = c (b - 1) + fInv (c (b + 1)) ∧
      (∀ j : ℕ, b < j →
        cbcBlockDecrypt fInv (dropCipherBlock c b) j = cbcBlockDecrypt fInv c (j + 1)) :=
  pairBlockDecrypt_dropBlock (fun x y => x + fInv y) c hb
/-- **CFB dropped-block resynchronization**: dropping
  ciphertext block `b ≥ 1` leaves blocks `1 ≤ j < b` unchanged, corrupts block `b` to `f (c (b -
  1)) + c (b + 1)`, and resynchronizes every subsequent block `j > b` to the shifted plaintext
  block `cfbBlockDecrypt f c (j + 1)`. -/
theorem cfbBlockDecrypt_dropBlock (f : BitString n → BitString n) (c : ℕ → BitString n)
    (b : ℕ) (hb : 1 ≤ b) :
    (∀ j : ℕ, 1 ≤ j → j < b →
      cfbBlockDecrypt f (dropCipherBlock c b) j = cfbBlockDecrypt f c j) ∧
      cfbBlockDecrypt f (dropCipherBlock c b) b = f (c (b - 1)) + c (b + 1) ∧
      (∀ j : ℕ, b < j →
        cfbBlockDecrypt f (dropCipherBlock c b) j = cfbBlockDecrypt f c (j + 1)) :=
  pairBlockDecrypt_dropBlock (fun x y => f x + y) c hb
/-- **OFB / CTR dropped-block permanent desynchronization ([KatzLindell2020], Exercise 3.30)**:
  dropping ciphertext block `b ≥ 1` leaves blocks `1 ≤ j < b` unchanged, but shifts every block
  `j ≥ b` by the keystream misalignment `mask iv j + mask iv (j + 1)`. -/
theorem maskBlockDecrypt_dropBlock (mask : BitString n → ℕ → BitString n) (iv : BitString n)
    (c : ℕ → BitString n) (b : ℕ) :
    (∀ j : ℕ, 1 ≤ j → j < b →
      maskBlockDecrypt mask iv (dropCipherBlock c b) j = maskBlockDecrypt mask iv c j) ∧
      (∀ j : ℕ, b ≤ j →
        maskBlockDecrypt mask iv (dropCipherBlock c b) j =
          maskBlockDecrypt mask iv c (j + 1) + (mask iv j + mask iv (j + 1))) := by
  refine ⟨fun j _ hjb => by simp [maskBlockDecrypt, dropCipherBlock, hjb], fun j hbj => ?_⟩
  simpa only [maskBlockDecrypt, dropCipherBlock, not_lt.mpr hbj, ↓reduceIte] using
    maskBlockDecrypt_changeIV (fun v _ => v) (mask iv (j + 1)) (mask iv j) c (j + 1)
end Cslib.Crypto
