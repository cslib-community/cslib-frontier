/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.CBCMode.Uniform
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Computational.LubyRackoff
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontierTests.Crypto.CTRModeUniform
import Mathlib.Data.Nat.Choose.Basic

/-!
# Tests for uniform random-IV CBC mode

Checks for `CslibFrontier/Crypto/Computational/Encryption/CBCMode/Uniform.lean`:
- concrete CBC encryption/decryption and round-trip inversion for a non-involution `BlockCipher`
  (`revXorCipher`, XORing the key and reversing each block);
- `BlockCipher.isPPTOn_cbcEncrypt`, `BlockCipher.computableInPolyTime_cbcDecrypt` and
  `BlockCipher.isOraclePPT_cbcToPrpDistinguisher` certificates;
- non-vacuous concrete block-cipher CPA bound at `n = 16` with additive term strictly below `1`;
- asymptotic CPA security theorem (`BlockCipher.PRP.indcpa_cbcEncrypt`), instantiated on
  `lubyRackoffCipher` (`keyLen n = 3 * n`, `blockLen n = 2 * n`);
- a negative/non-vacuity witness showing that with the identity `BlockCipher` `idBlockCipher`
  (`encrypt _ _ x = x`, which has super-polynomial block space `2 ^ n` but is not a `PRP`),
  random-IV CBC (`idBlockCipher.cbcEncrypt`) is **not** CPA-secure
  (`not_indcpa_cbcEncrypt_idBlockCipher`), via an explicit 2-block chosen-plaintext distinguisher
  (`(0ⁿ ++ 0ⁿ, 0ⁿ ++ 1ⁿ)`).
-/

public section

namespace CslibFrontierTests.Crypto.CBCModeUniform

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.Crypto.CTRModeUniform

/-! ### A concrete non-involution `BlockCipher` -/

/-- A toy `BlockCipher` with `keyLen = id` and `blockLen = id`: encryption XORs the key with the
block and reverses the bits; decryption reverses first and then XORs the key. For non-palindromic
keys `encrypt ≠ decrypt`. -/
@[expose]
def revXorCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ k x := (List.zipWith xor k x).reverse
  decrypt _ k y := List.zipWith xor k y.reverse
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt n k x hk hx := by simp [hk, hx]
  length_decrypt n k y hk hy := by simp [hk, hy]
  decrypt_encrypt n k x hk hx := by
    rw [List.reverse_reverse]
    exact BitString.zipWith_xor_self_left k x (hk.trans hx.symm)
  encrypt_decrypt n k y hk hy := by
    rw [BitString.zipWith_xor_self_left k y.reverse (by simp [hk, hy]), List.reverse_reverse]

/-- Under key `[true, false]` (`n = 2`), encryption and decryption of `revXorCipher` are distinct
operations: `encrypt 2 [true, false] [false, false] = [false, true]` whereas
`decrypt 2 [true, false] [false, false] = [true, false]`. -/
example :
    revXorCipher.encrypt 2 [true, false] [false, false] = [false, true] ∧
    revXorCipher.decrypt 2 [true, false] [false, false] = [true, false] := by
  decide

/-- Concrete 3-block CBC encryption and decryption from `iv = [true, true]` under `revXorCipher`
with key `[true, false]`, plus rejection of malformed ciphertexts. -/
example :
    let enc := fun k x => revXorCipher.encrypt k.length k x
    let dec := fun k y => revXorCipher.decrypt k.length k y
    let iv := [true, true]
    let k := [true, false]
    let msg := [true, false, false, true, true, true]
    let ct := iv ++ cbcWordBody enc 2 k iv msg
    cbcWordDecrypt dec 2 k ct = some msg ∧
      cbcWordDecrypt dec 2 k [] = none ∧
      cbcWordDecrypt dec 2 k [true, true, false] = none := by
  decide

/-- Round-trip decryption for `revXorCipher` on a 3-block message over all random IVs in support. -/
example {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (revXorCipher.cbcEncrypt 2 [true, false]
      [true, false, false, true, true, true])).support) :
    revXorCipher.cbcDecrypt 2 [true, false] ct =
      some [true, false, false, true, true, true] :=
  revXorCipher.cbcDecrypt_cbcEncrypt (n := 2) (k := [true, false]) rfl (by decide) hct

/-! ### Efficiency certificates for honest algorithms and reduction -/

/-- `revXorCipher.cbcEncrypt` is uniformly strict PPT. -/
example :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ((n, k, msg) : ℕ × List Bool × List Bool) => revXorCipher.cbcEncrypt n k msg) :=
  revXorCipher.isPPTOn_cbcEncrypt

/-- `revXorCipher.cbcDecrypt` is computable in polynomial time. -/
example :
    ComputableInPolyTime
      (fun ((n, k, ct) : ℕ × List Bool × List Bool) => revXorCipher.cbcDecrypt n k ct)
      (encKeyedInput encBits) (encOption encBits) :=
  revXorCipher.computableInPolyTime_cbcDecrypt

/-- The block-cipher reduction built from `oneBlockAdversary` is uniform strict oracle PPT. -/
example :
    IsOraclePPT encBool (revXorCipher.cbcToPrpDistinguisher oneBlockAdversary false) :=
  revXorCipher.isOraclePPT_cbcToPrpDistinguisher isOraclePPT_oneBlockAdversary false

/-! ### Non-vacuous concrete bound at `n = 16` -/

/-- At `n = 16`, the concrete block-cipher CPA bound for `revXorCipher` and
`oneBlockAdversary` (`Q = 1`, `L = 50`) has additive term
`4 * (50.choose 2 / 2 ^ 16) = 4900 / 65536 < 1`. -/
example :
    (Game.advantage
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (revXorCipher.blockLen m))
        (fun m => BitString.sampleList (revXorCipher.keyLen m))
        revXorCipher.cbcEncrypt oneBlockAdversary false 16))
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (revXorCipher.blockLen m))
        (fun m => BitString.sampleList (revXorCipher.keyLen m))
        revXorCipher.cbcEncrypt oneBlockAdversary true 16)) : ℝ) ≤
      (Game.advantage
        (ProbComp.eval
          (revXorCipher.prpRealGame
            (revXorCipher.cbcToPrpDistinguisher oneBlockAdversary false) 16))
        (ProbComp.eval
          (prpIdealGame revXorCipher.blockLen
            (revXorCipher.cbcToPrpDistinguisher oneBlockAdversary false) 16)) : ℝ) +
      (Game.advantage
        (ProbComp.eval
          (revXorCipher.prpRealGame
            (revXorCipher.cbcToPrpDistinguisher oneBlockAdversary true) 16))
        (ProbComp.eval
          (prpIdealGame revXorCipher.blockLen
            (revXorCipher.cbcToPrpDistinguisher oneBlockAdversary true) 16)) : ℝ) +
      4 * (((1 * 50).choose 2 : ℝ) / 2 ^ revXorCipher.blockLen 16) ∧
    4 * (((1 * 50).choose 2 : ℝ) / 2 ^ revXorCipher.blockLen 16) < 1 :=
  ⟨revXorCipher.advantage_cbcEncrypt_le oneBlockAdversary
      (isQueryBounded_oneBlockAdversary 16) (queriesSatisfy_oneBlockAdversary 16),
    by norm_num [revXorCipher, Nat.choose]⟩

/-! ### Asymptotic security theorem (including non-`id` Luby–Rackoff instantiation) -/

open scoped NNReal in
/-- Random-IV CBC mode is CPA-secure for every `BlockCipher.PRP` with super-polynomial block space
([BonehShoup2023], Theorem 5.4). -/
example {E : BlockCipher} (hprp : E.PRP)
    (hneg : Negligible fun n => ((2 : ℝ≥0) ^ E.blockLen n)⁻¹) :
    SymmetricINDCPAOn (fun n => blockPairValid (E.blockLen n))
      (fun n => BitString.sampleList (E.keyLen n)) E.cbcEncrypt :=
  hprp.indcpa_cbcEncrypt hneg

/-- End-to-end instantiation of Theorems 4.9 + 5.4 with non-`id` key and block schedules: for any
`PseudorandomFunction family`, random-IV CBC mode over the 3-round Luby–Rackoff cipher
(`keyLen n = 3 * n`, `blockLen n = 2 * n`) is CPA-secure. -/
example {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family) :
    let E := lubyRackoffCipher family hfamily.polyTime hfamily.length_eq
    SymmetricINDCPAOn (fun n => blockPairValid (E.blockLen n))
      (fun n => BitString.sampleList (E.keyLen n)) E.cbcEncrypt :=
  hfamily.prp_lubyRackoffCipher.indcpa_cbcEncrypt
    (negligible_inv_two_pow_comp_of_le fun n => by dsimp only [lubyRackoffCipher]; omega)

/-! ### Insecurity of random-IV CBC with the identity block cipher -/

/-- The identity `BlockCipher` (`keyLen = id`, `blockLen = id`, `encrypt _ _ x = x`,
`decrypt _ _ y = y`), which has super-polynomial block space `2 ^ n` (`Negligible (2 ^ n)⁻¹`) but
is not a `PRP`. -/
@[expose]
def idBlockCipher : BlockCipher where
  keyLen := id
  blockLen := id
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := ComputableInPolyTime.id'
  encrypt _ _ x := x
  decrypt _ _ y := y
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ _ hx := hx
  length_decrypt _ _ _ _ hy := hy
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

/-- Two-block CPA distinguisher against random-IV CBC with `idBlockCipher`: submit
`(0ⁿ ++ 0ⁿ, 0ⁿ ++ 1ⁿ)` and test whether the two ciphertext blocks `c₁` and `c₂` after the IV are
equal. Under `E(k, x) = x`, `0ⁿ ++ 0ⁿ` always gives `c₁ = iv = c₂`, whereas `0ⁿ ++ 1ⁿ` gives
`c₁ = iv` and `c₂ = iv ⊕ 1ⁿ ≠ c₁` for every `n ≥ 1`. -/
def twoBlockIdAttack : OracleDistinguisher :=
  fun n _ =>
    (fun reply => (reply.drop n).take n == reply.drop (2 * n)) <$>
      (List.take (3 * n) <$> ProbOracleComp.query
        ((), encPair encBits encBits
          (List.replicate (2 * n) false,
           List.replicate n false ++ List.replicate n true)))

theorem isOraclePPT_twoBlockIdAttack : IsOraclePPT encBool twoBlockIdAttack := by
  have hrequest : ComputableInPolyTime
      (fun p : ℕ × List Bool =>
        encPair encBits encBits
          (List.replicate (2 * p.1) false,
           List.replicate p.1 false ++ List.replicate p.1 true))
      (encPair encUnary encBits) encBits := by
    polytime
  have hlimit : ComputableInPolyTime (fun p : ℕ × List Bool => 3 * p.1)
      (encPair encUnary encBits) encUnary := by
    polytime
  have hout : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool =>
        (p.2.drop p.1.1).take p.1.1 == p.2.drop (2 * p.1.1))
      (encPair (encPair encUnary encBits) encBits) encBool := by
    polytime
  unfold twoBlockIdAttack
  exact ((IsOraclePPTOn.query_take' () hrequest hlimit).map_with' hout).isOraclePPT

private theorem zipWith_xor_replicate_false :
    ∀ (u : List Bool) {n : ℕ}, u.length = n → List.zipWith xor u (List.replicate n false) = u
  | [], 0, _ => rfl
  | b :: u, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [List.replicate_succ, zipWith_xor_replicate_false u h]

private theorem ne_zipWith_xor_replicate_true {u : List Bool} {n : ℕ} (hn : 0 < n)
    (hu : u.length = n) : u ≠ List.zipWith xor u (List.replicate n true) := by
  cases u with
  | nil => simp at hu; omega
  | cons b u =>
    cases n with
    | zero => omega
    | succ n =>
      intro heq
      have hhead := congrArg List.head? heq
      cases b <;> simp [List.replicate_succ] at hhead

private theorem listRows_two_blocks {n : ℕ} {b₁ b₂ : List Bool} (hb₁ : b₁.length = n)
    (hb₂ : b₂.length = n) :
    BitString.listRows 2 n (b₁ ++ b₂) = [b₁, b₂] := by
  have h1 : BitString.listRows 1 n b₂ = [b₂] := by
    simpa [BitString.listRows] using BitString.listRows_succ_append 0 n hb₂ []
  rw [BitString.listRows_succ_append 1 n hb₁ b₂, h1]

private theorem eval_cpaGame_id_twoBlockIdAttack {n : ℕ} (hn : 0 < n) (bit : Bool) :
    ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun _ x => x) twoBlockIdAttack bit n) =
      PMF.pure (!bit) := by
  have hvalid : blockPairValid n (List.replicate (2 * n) false)
      (List.replicate n false ++ List.replicate n true) = true := by
    simp [blockPairValid, Nat.two_mul, Nat.add_mod_right]
  let test (ct : List Bool) : Bool :=
    ((ct.take (3 * n)).drop n).take n == (ct.take (3 * n)).drop (2 * n)
  let msg : List Bool :=
    if bit then List.replicate n false ++ List.replicate n true
    else List.replicate (2 * n) false
  have hbody_indep (k : List Bool) :
      cbcWordBody (fun _ x => x) n k = cbcWordBody (fun _ x => x) n [] := rfl
  have hgame : ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun _ x => x) twoBlockIdAttack bit n) =
      (BitString.uniformList n).bind fun iv =>
        PMF.pure (test (iv ++ cbcWordBody (fun _ x => x) n [] iv msg)) := by
    simp only [symmetricCPAGameOn, symmetricCPAReplyOn, twoBlockIdAttack, encPair_apply,
      encBits_apply, unframe_frame_append, dropFrame_frame_append, hvalid, ↓reduceIte,
      ProbOracleComp.run_map, ProbOracleComp.run_query, cbcWordEncrypt, ivModeEncrypt,
      hbody_indep, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.bind_const, Function.comp_def, ← PMF.bind_pure_comp,
      PMF.bind_bind, PMF.pure_bind, test, msg]
  rw [hgame]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (!bit)) fun iv hiv => ?_).trans
    (PMF.bind_const _ _)
  congr 1
  have hivLen : iv.length = n := BitString.length_of_mem_support_uniformList hiv
  have hdiv : 2 * n / n = 2 := Nat.mul_div_cancel 2 hn
  cases bit
  · have hm₀ : List.replicate (2 * n) false =
        List.replicate n false ++ List.replicate n false := by
      rw [Nat.two_mul, List.replicate_add]
    have hrows : BitString.listRows ((List.replicate (2 * n) false).length / n) n
        (List.replicate (2 * n) false) = [List.replicate n false, List.replicate n false] := by
      rw [List.length_replicate, hdiv, hm₀]
      exact listRows_two_blocks List.length_replicate List.length_replicate
    have hbody : cbcWordBody (fun _ x => x) n [] iv (List.replicate (2 * n) false) = iv ++ iv := by
      unfold cbcWordBody
      rw [hrows]
      simp only [List.foldl_cons, List.foldl_nil, zipWith_xor_replicate_false iv hivLen,
        List.take_of_length_le hivLen.le, List.nil_append]
    have htake3 : (iv ++ (iv ++ iv)).take (3 * n) = iv ++ (iv ++ iv) :=
      List.take_of_length_le (by simp [hivLen]; omega)
    have hdrop2 : (iv ++ (iv ++ iv)).drop (2 * n) = iv := by
      rw [Nat.two_mul, ← List.drop_drop, ← hivLen, List.drop_left, List.drop_left]
    have hdrop1 : ((iv ++ (iv ++ iv)).drop n).take n = iv := by
      rw [← hivLen, List.drop_left, List.take_left]
    dsimp only [test, msg]
    rw [ite_eq_right Bool.false_ne_true, hbody, htake3, hdrop1, hdrop2]
    simp
  · have hlen₁ : (List.replicate n false ++ List.replicate n true).length = 2 * n := by
      simp [Nat.two_mul]
    have hrows : BitString.listRows
        ((List.replicate n false ++ List.replicate n true).length / n) n
        (List.replicate n false ++ List.replicate n true) =
        [List.replicate n false, List.replicate n true] := by
      rw [hlen₁, hdiv]
      exact listRows_two_blocks List.length_replicate List.length_replicate
    set c₂ := List.zipWith xor iv (List.replicate n true)
    have hc₂Len : c₂.length = n := by simp [c₂, hivLen]
    have hbody : cbcWordBody (fun _ x => x) n [] iv
        (List.replicate n false ++ List.replicate n true) = iv ++ c₂ := by
      unfold cbcWordBody
      rw [hrows]
      simp only [List.foldl_cons, List.foldl_nil, c₂, zipWith_xor_replicate_false iv hivLen,
        List.take_of_length_le hivLen.le, List.take_of_length_le hc₂Len.le, List.nil_append]
    have htake3 : (iv ++ (iv ++ c₂)).take (3 * n) = iv ++ (iv ++ c₂) :=
      List.take_of_length_le (by simp [hivLen, hc₂Len]; omega)
    have hdrop2 : (iv ++ (iv ++ c₂)).drop (2 * n) = c₂ := by
      rw [Nat.two_mul, ← List.drop_drop, ← hivLen, List.drop_left, List.drop_left]
    have hdrop1 : ((iv ++ (iv ++ c₂)).drop n).take n = iv := by
      rw [← hivLen, List.drop_left, List.take_left]
    dsimp only [test, msg]
    rw [ite_eq_left rfl, hbody, htake3, hdrop1, hdrop2]
    exact beq_eq_false_iff_ne.mpr (ne_zipWith_xor_replicate_true hn hivLen)

/-- **Non-vacuity of the `BlockCipher.PRP` hypothesis:** with `idBlockCipher` (`encrypt _ _ x = x`),
random-IV CBC mode `idBlockCipher.cbcEncrypt` is **not** CPA-secure (`twoBlockIdAttack` achieves
advantage `1` for every `n ≥ 1`). -/
theorem not_indcpa_cbcEncrypt_idBlockCipher :
    ¬ SymmetricINDCPAOn (fun n => blockPairValid (idBlockCipher.blockLen n))
      (fun n => BitString.sampleList (idBlockCipher.keyLen n)) idBlockCipher.cbcEncrypt := by
  intro hsec
  have hneg := (hsec twoBlockIdAttack isOraclePPT_twoBlockIdAttack).shift 1
  have hadv (n : ℕ) : Game.advantage
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (idBlockCipher.blockLen m))
        (fun m => BitString.sampleList (idBlockCipher.keyLen m))
        idBlockCipher.cbcEncrypt twoBlockIdAttack false (n + 1)))
      (ProbComp.eval (symmetricCPAGameOn (fun m => blockPairValid (idBlockCipher.blockLen m))
        (fun m => BitString.sampleList (idBlockCipher.keyLen m))
        idBlockCipher.cbcEncrypt twoBlockIdAttack true (n + 1))) = 1 := by
    change Game.advantage
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun _ x => x) twoBlockIdAttack false (n + 1)))
      (ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
        (cbcWordEncrypt fun _ x => x) twoBlockIdAttack true (n + 1))) = 1
    rw [eval_cpaGame_id_twoBlockIdAttack (Nat.succ_pos n) false,
      eval_cpaGame_id_twoBlockIdAttack (Nat.succ_pos n) true]
    simp [Game.succProbability]
  exact not_negligible_const (c := 1) one_ne_zero (by simpa only [hadv] using hneg)

end CslibFrontierTests.Crypto.CBCModeUniform
