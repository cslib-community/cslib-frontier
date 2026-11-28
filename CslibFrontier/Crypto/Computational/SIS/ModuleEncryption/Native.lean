/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption
public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Computability.PolyTime.Int.Negacyclic
import CslibFrontier.Crypto.Computational.SIS.Native
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.ZMod.DotProduct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native realization of existing Module-LWE key generation and decryption

One total word implementation realizes `moduleLWEKeyGen` in the existing
`ModuleLWE.encodeSample` codec, and one total word implementation realizes
`moduleLWEDecrypt` over existing ciphertext matrices and secret integer lists.
Both dimensions are unary runtime inputs; the modulus and coefficients are binary.
Runtime charges all input words, including discarded data. Canonical interpretation
requires a positive modulus.

## Main results

* `exists_computableInPolyTime_moduleLWEKeyGen`: a single native implementation for all
  dimensions, positive moduli, structured matrices and signed integer secret/error lifts.
* `exists_computableInPolyTime_moduleLWEDecrypt`: a single native implementation for all
  dimensions, positive moduli, signed integer secrets and structured ciphertexts.

This is original implementation algebra. It supplies neither native matrix sampling nor a
malformed-input rejection policy, encryption implementation or security theorem.
-/

public section

open scoped Matrix

namespace Cslib.Crypto

open Turing.MultiTapeTM Mathlib.Tactic.Matrix

private abbrev KeyGenInput := ((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool

private def keyGenInputEncoding : KeyGenInput ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encNat)
    (encPair encBits (encPair encBits encBits))

private def keyGenCoefficients (d q : ℕ) (rows : List (List ℕ)) (s e : List ℤ) : List ℕ :=
  (List.range d).map fun i =>
    ((ListMatrix.dotProduct d ((rows.getD i []).map (fun x : ℕ => (x : ℤ))) s +
      e.getD i 0) % (q : ℤ)).toNat

private theorem keyGenCoefficients_polyTime :
    ComputableInPolyTime
      (fun a : (ℕ × ℕ) × List (List ℕ) × List ℤ × List ℤ =>
        keyGenCoefficients a.1.1 a.1.2 a.2.1 a.2.2.1 a.2.2.2)
      (encPair (encPair encUnary encNat)
        (encPair (encList (encList encNat)) (encPair (encList encIntBin) (encList encIntBin))))
      (encList encNat) := by
  unfold keyGenCoefficients
  have hcast := ComputableInPolyTime.intBin_natCast
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · fun_prop
  · apply ComputableInPolyTime.intBin_emodNat'
    · fun_prop
    · fun_prop

private def keyGenWords (a : KeyGenInput) : List Bool :=
  encPair encBits (encList encNat) (a.2.1,
    keyGenCoefficients (a.1.1.1 * a.1.1.2) a.1.2
      ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.1)
      ((Decoder.list Decoder.intBin).decode a.2.2.1)
      ((Decoder.list Decoder.intBin).decode a.2.2.2))

private theorem keyGenWords_polyTime :
    ComputableInPolyTime keyGenWords keyGenInputEncoding encBits := by
  have hrows := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime
  have hdecode := (Decoder.list Decoder.intBin).computableInPolyTime
  have hcoeff := keyGenCoefficients_polyTime
  have hinput : ComputableInPolyTime
      (fun a : KeyGenInput => (((a.1.1.1 * a.1.1.2), a.1.2),
        ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.1,
          (Decoder.list Decoder.intBin).decode a.2.2.1,
          (Decoder.list Decoder.intBin).decode a.2.2.2)))
      keyGenInputEncoding
      (encPair (encPair encUnary encNat)
        (encPair (encList (encList encNat))
          (encPair (encList encIntBin) (encList encIntBin)))) := by
    unfold keyGenInputEncoding
    apply ComputableInPolyTime.prod
    · fun_prop
    · exact (hrows.comp (by fun_prop)).prod
        ((hdecode.comp (by fun_prop)).prod (hdecode.comp (by fun_prop)))
  have h := (show ComputableInPolyTime (fun a : KeyGenInput => a.2.1)
      keyGenInputEncoding encBits by unfold keyGenInputEncoding; fun_prop).prod
    (hcoeff.comp hinput)
  exact h.of_enc_eq fun _ => rfl

private theorem keyGenCoefficients_ofFn {d q : ℕ} (hq : 0 < q)
    (A : _root_.Matrix (Fin d) (Fin d) (ZMod q)) (s e : Fin d → ℤ) :
    keyGenCoefficients d q (List.ofFn fun i => List.ofFn fun j => (A i j).val)
      (List.ofFn s) (List.ofFn e) =
    List.ofFn (fun i => ((A *ᵥ (Int.cast ∘ s)) i + (e i : ZMod q)).val) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [keyGenCoefficients, List.map_range_eq_ofFn]
  congr 1 with i : 1
  simp only [List.getD_ofFn, List.map_ofFn, Function.comp_def]
  have h := ListMatrix.intCast_dotProduct_matrix_ofFn A s i
  simp only [List.getD_ofFn, ZMod.cast_eq_val, Function.comp_def] at h
  rw [← h, ← Int.cast_add]
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := q)
    (ListMatrix.dotProduct d (List.ofFn fun j => ((A i j).val : ℤ)) (List.ofFn s) + e i))
  simpa only [Int.toNat_natCast] using hv.symm

private theorem keyGenWords_encode {k n q : ℕ} (hq : 0 < q)
    (A : _root_.Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ℤ) :
    keyGenWords (((k, n), q), (ModuleSIS.encodeMatrix A,
      (ModuleSIS.encodeVec s, ModuleSIS.encodeVec e))) =
      ModuleLWE.encodeSample
        (moduleLWEKeyGen A (fun j i => (s j i : ZMod q)) (fun j i => (e j i : ZMod q))) := by
  simp only [keyGenWords, ModuleSIS.encodeMatrix, ModuleSIS.encodeVec,
    SIS.encodeMatrix, SIS.encodeVec, Decoder.decode_enc]
  rw [keyGenCoefficients_ofFn hq]
  simp only [ModuleLWE.encodeSample, moduleLWEKeyGen_eq_sample,
    ModuleLWE.flattenPolyVec_sample, ← intCast_comp_flattenPolyVec]
  rfl

/-- A single total native function realizes existing deterministic Module-LWE key generation
in its existing expanded-matrix/public-sample codec. Dimensions are unary; the modulus and
all coefficient words are binary. The certificate charges the full raw input. No sampling
or canonicality test is included; semantic equality holds for canonical inputs and `q > 0`. -/
theorem exists_computableInPolyTime_moduleLWEKeyGen :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits (encPair encBits encBits))) encBits ∧
      ∀ (k n q : ℕ) (_hq : 0 < q)
        (A : _root_.Matrix (Fin k) (Fin k) (Fin n → ZMod q))
        (s e : Fin k → Fin n → ℤ),
        run (((k, n), q), (ModuleSIS.encodeMatrix A,
          (ModuleSIS.encodeVec s, ModuleSIS.encodeVec e))) =
          ModuleLWE.encodeSample
            (moduleLWEKeyGen A (fun j i => (s j i : ZMod q))
              (fun j i => (e j i : ZMod q))) :=
  ⟨keyGenWords, keyGenWords_polyTime, fun _ _ _ hq A s e => keyGenWords_encode hq A s e⟩

private abbrev DecryptInput := ((ℕ × ℕ) × ℕ) × List Bool × List Bool

private def decryptInputEncoding : DecryptInput ↪ List Bool :=
  encPair (encPair (encPair encUnary encUnary) encNat)
    (encPair encBits encBits)

private def decryptSecretCoeffs (n q : ℕ) (s_ints : List ℤ) (j : ℕ) : List ℕ :=
  (List.range n).map fun l => ((s_ints.getD (j * n + l) 0) % (q : ℤ)).toNat

private theorem decryptSecretCoeffs_polyTime :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × List ℤ) × ℕ =>
        decryptSecretCoeffs p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary)
      (encList encNat) := by
  unfold decryptSecretCoeffs
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · fun_prop
  · apply ComputableInPolyTime.intBin_emodNat'
    · fun_prop
    · fun_prop

private def decryptProducts (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) :
    List (List ℕ) :=
  (List.range k).map fun j =>
    negacyclicMulResidues n q (ct_rows.getD (j + 1) []) (decryptSecretCoeffs n q s_ints j)

private theorem decryptProducts_polyTime :
    ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ =>
        decryptProducts a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      (encList (encList encNat)) := by
  unfold decryptProducts
  have hmul := computableInPolyTime_negacyclicMulResidues
  have hsec := decryptSecretCoeffs_polyTime
  apply ComputableInPolyTime.mapWithInput (encA := encUnary)
  · fun_prop
  · let encP := encPair (encPair (encPair (encPair encUnary encUnary) encNat)
      (encPair (encList (encList encNat)) (encList encIntBin))) encUnary
    have hsec_in : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          (((p.1.1.1.2, p.1.1.2), p.1.2.2), p.2))
        encP (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encUnary) := by
      fun_prop
    have hs : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          decryptSecretCoeffs p.1.1.1.2 p.1.1.2 p.1.2.2 p.2)
        encP (encList encNat) := hsec.comp hsec_in
    have hmul_in : ComputableInPolyTime
        (fun p : (((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) × ℕ =>
          ((p.1.1.1.2, p.1.1.2),
            (p.1.2.1.getD (p.2 + 1) [], decryptSecretCoeffs p.1.1.1.2 p.1.1.2 p.1.2.2 p.2)))
        encP (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat))) := by
      fun_prop
    simpa only [Function.comp_def] using hmul.comp hmul_in

private def columnSum (prods : List (List ℕ)) (i : ℕ) : ℕ :=
  (prods.map fun row => row.getD i 0).sum

private theorem columnSum_polyTime :
    ComputableInPolyTime (fun p : List (List ℕ) × ℕ => columnSum p.1 p.2)
      (encPair (encList (encList encNat)) encUnary) encNat := by
  unfold columnSum
  apply Turing.MultiTapeTM.ComputableInPolyTime.binary_sum.comp
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  fun_prop

private def decryptedBit (q v_i sum_i : ℕ) : Bool :=
  let diff := (((v_i : ℤ) - (sum_i : ℤ)) % (q : ℤ)).toNat
  decide (q / 4 < if diff ≤ q / 2 then diff else q - diff)

private theorem decryptedBit_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => decryptedBit p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encNat) encBool := by
  unfold decryptedBit
  have hcast := ComputableInPolyTime.intBin_natCast
  have hdiv := Turing.MultiTapeTM.ComputableInPolyTime.binary_div
  have hsub := Turing.MultiTapeTM.ComputableInPolyTime.binary_sub
  have hq : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.1)
      (encPair (encPair encNat encNat) encNat) encNat := by fun_prop
  have hdiff : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => (((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat)
      (encPair (encPair encNat encNat) encNat) encNat :=
    ComputableInPolyTime.intBin_emodNat' (by fun_prop) hq
  have hbound : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × ℕ =>
        let diff := (((p.1.2 : ℤ) - (p.2 : ℤ)) % (p.1.1 : ℤ)).toNat
        if diff ≤ p.1.1 / 2 then diff else p.1.1 - diff)
      (encPair (encPair encNat encNat) encNat) encNat :=
    ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.binary_le.comp (hdiff.prod (hdiv.comp (hq.prod (.const 2)))))
      hdiff (hsub.comp (hq.prod hdiff))
  exact ComputableInPolyTime.binary_lt.comp ((hdiv.comp (hq.prod (.const 4))).prod hbound)

private abbrev DecryptEnv := ((ℕ × ℕ) × List ℕ) × List (List ℕ)

private def decryptEnvEncoding : DecryptEnv ↪ List Bool :=
  encPair (encPair (encPair encUnary encNat) (encList encNat)) (encList (encList encNat))

private def makeDecryptEnv (a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ) : DecryptEnv :=
  (((a.1.1.2, a.1.2), a.2.1.getD 0 []), decryptProducts a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)

private theorem makeDecryptEnv_polyTime :
    ComputableInPolyTime makeDecryptEnv
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      decryptEnvEncoding := by
  unfold makeDecryptEnv decryptEnvEncoding
  have hprods := decryptProducts_polyTime
  fun_prop

private def decryptBitsFromEnv (e : DecryptEnv) : List Bool :=
  (List.range e.1.1.1).map fun i =>
    decryptedBit e.1.1.2 (e.1.2.getD i 0) (columnSum e.2 i)

private theorem decryptBitsFromEnv_polyTime :
    ComputableInPolyTime decryptBitsFromEnv decryptEnvEncoding encBits := by
  unfold decryptBitsFromEnv decryptEnvEncoding
  have hbit := decryptedBit_polyTime
  have hcol := columnSum_polyTime
  apply ComputableInPolyTime.mapToBitsWithInput (enc := encUnary)
  · fun_prop
  · let encP := encPair (encPair (encPair (encPair encUnary encNat) (encList encNat))
      (encList (encList encNat))) encUnary
    have hsum_in : ComputableInPolyTime (fun p : DecryptEnv × ℕ => (p.1.2, p.2))
        encP (encPair (encList (encList encNat)) encUnary) := by fun_prop
    have hsum : ComputableInPolyTime (fun p : DecryptEnv × ℕ => columnSum p.1.2 p.2)
        encP encNat := hcol.comp hsum_in
    have hbit_in : ComputableInPolyTime
        (fun p : DecryptEnv × ℕ => ((p.1.1.1.2, p.1.1.2.getD p.2 0), columnSum p.1.2 p.2))
        encP (encPair (encPair encNat encNat) encNat) := by fun_prop
    simpa only [Function.comp_def] using hbit.comp hbit_in

private def decryptBits (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) : List Bool :=
  decryptBitsFromEnv (makeDecryptEnv (((k, n), q), ct_rows, s_ints))

private theorem decryptBits_def (k n q : ℕ) (ct_rows : List (List ℕ)) (s_ints : List ℤ) :
    decryptBits k n q ct_rows s_ints =
      (List.range n).map fun i =>
        decryptedBit q ((ct_rows.getD 0 []).getD i 0)
          (columnSum (decryptProducts k n q ct_rows s_ints) i) :=
  rfl

private theorem decryptBits_polyTime :
    ComputableInPolyTime
      (fun a : ((ℕ × ℕ) × ℕ) × List (List ℕ) × List ℤ =>
        decryptBits a.1.1.1 a.1.1.2 a.1.2 a.2.1 a.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin)))
      encBits := by
  have h := decryptBitsFromEnv_polyTime.comp makeDecryptEnv_polyTime
  simpa only [Function.comp_def, decryptBits] using h

private def decryptWords (a : DecryptInput) : List Bool :=
  decryptBits a.1.1.1 a.1.1.2 a.1.2
    ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.2)
    ((Decoder.list Decoder.intBin).decode a.2.1)

private theorem decryptWords_polyTime :
    ComputableInPolyTime decryptWords decryptInputEncoding encBits := by
  unfold decryptWords
  have hct := (Decoder.list (Decoder.list Decoder.nat)).computableInPolyTime
  have hs := (Decoder.list Decoder.intBin).computableInPolyTime
  have hinput : ComputableInPolyTime
      (fun a : DecryptInput =>
        (a.1, ((Decoder.list (Decoder.list Decoder.nat)).decode a.2.2,
          (Decoder.list Decoder.intBin).decode a.2.1)))
      decryptInputEncoding
      (encPair (encPair (encPair encUnary encUnary) encNat)
        (encPair (encList (encList encNat)) (encList encIntBin))) := by
    unfold decryptInputEncoding
    apply ComputableInPolyTime.prod
    · fun_prop
    · exact (hct.comp (by fun_prop)).prod (hs.comp (by fun_prop))
  have h := decryptBits_polyTime.comp hinput
  exact h

private theorem valMinAbs_natAbs {q : ℕ} (hq : 0 < q) (x : ZMod q) :
    x.valMinAbs.natAbs = if x.val ≤ q / 2 then x.val else q - x.val := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [ZMod.valMinAbs_def_pos]
  split_ifs with h
  · exact Int.natAbs_natCast x.val
  · have heq : ((x.val : ℤ) - q) = - ((q - x.val : ℕ) : ℤ) := by
      have hlt := ZMod.val_lt x
      omega
    rw [heq, Int.natAbs_neg, Int.natAbs_natCast]

private theorem zmod_val_intCast {q : ℕ} (hq : 0 < q) (z : ℤ) :
    (z : ZMod q).val = (z % (q : ℤ)).toNat := by
  let : NeZero q := ⟨hq.ne'⟩
  have hv := congrArg Int.toNat (ZMod.val_intCast (n := q) z)
  simpa only [Int.toNat_natCast] using hv

private theorem decryptSecretCoeffs_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (j : Fin k) :
    decryptSecretCoeffs n q (List.ofFn (flattenPolyVec s)) j.val =
      List.ofFn fun l : Fin n => (s j l : ZMod q).val := by
  unfold decryptSecretCoeffs
  rw [List.map_range_eq_ofFn]
  congr 1 with l : 1
  have hidx : (finProdFinEquiv (j, l)).val = j.val * n + l.val := by
    simp [finProdFinEquiv, mul_comm, add_comm]
  rw [← hidx, List.getD_ofFn, flattenPolyVec_apply, zmod_val_intCast hq]

private theorem decryptProducts_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptProducts k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s)) =
      List.ofFn fun j : Fin k => List.ofFn fun l : Fin n =>
        (negacyclicMul (ct.1 j) (fun l => (s j l : ZMod q)) l).val := by
  unfold decryptProducts
  rw [List.map_range_eq_ofFn]
  congr 1 with j : 1
  have hu : (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n =>
      (extendCiphertext ct i j).val).getD (j.val + 1) [] =
      List.ofFn fun l : Fin n => (ct.1 j l).val := by
    rw [← Fin.val_succ, List.getD_ofFn]
    rfl
  rw [hu, decryptSecretCoeffs_ofFn hq s j]
  exact negacyclicMulResidues_ofFn hq (ct.1 j) (fun l => (s j l : ZMod q))

private theorem columnSum_decryptProducts_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) (i : Fin n) :
    ((columnSum (decryptProducts k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s))) i.val : ZMod q)) =
      (innerPoly ct.1 (fun j l => (s j l : ZMod q))) i := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [decryptProducts_ofFn hq s ct]
  unfold columnSum innerPoly
  simp only [List.map_ofFn, Function.comp_def, List.getD_ofFn, List.sum_ofFn, Nat.cast_sum,
    ZMod.natCast_zmod_val, Finset.sum_apply]

private theorem decryptBits_ofFn {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptBits k n q
      (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
      (List.ofFn (flattenPolyVec s)) =
      List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [decryptBits_def, List.map_range_eq_ofFn]
  congr 1 with i : 1
  have hv : (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n =>
      (extendCiphertext ct i j).val).getD 0 [] =
      List.ofFn fun l : Fin n => (ct.2 l).val := by
    change (List.ofFn _).getD (0 : Fin (k + 1)).val [] = _
    rw [List.getD_ofFn]
    rfl
  simp only [hv, List.getD_ofFn]
  unfold decryptedBit
  set sum_i := columnSum (decryptProducts k n q
    (List.ofFn fun i : Fin (k + 1) => List.ofFn fun j : Fin n => (extendCiphertext ct i j).val)
    (List.ofFn (flattenPolyVec s))) i.val
  set w := ct.2 - innerPoly ct.1 (fun j l => (s j l : ZMod q))
  have hdiff_cast : ((((ct.2 i).val : ℤ) - (sum_i : ℤ) : ZMod q)) = w i := by
    push_cast
    rw [ZMod.natCast_zmod_val, columnSum_decryptProducts_ofFn hq s ct i]
    rfl
  have hdiff_nat : ((((ct.2 i).val : ℤ) - (sum_i : ℤ)) % (q : ℤ)).toNat = (w i).val := by
    rw [← zmod_val_intCast hq, Int.cast_sub, hdiff_cast]
  dsimp only
  rw [hdiff_nat, ← valMinAbs_natAbs hq (w i)]
  rfl

private theorem decryptWords_encode {k n q : ℕ} (hq : 0 < q)
    (s : Fin k → Fin n → ℤ) (ct : ModuleLWECiphertext k n q) :
    decryptWords (((k, n), q), (ModuleSIS.encodeVec s,
      SIS.encodeMatrix (extendCiphertext ct))) =
      List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) := by
  simp only [decryptWords, ModuleSIS.encodeVec, SIS.encodeMatrix,
    SIS.encodeVec, Decoder.decode_enc]
  exact decryptBits_ofFn hq s ct

/-- A single total native function realizes existing deterministic Module-LWE decryption
over unary rank/degree, binary modulus and complete existing secret/ciphertext words,
agreeing with `moduleLWEDecrypt` on canonical inputs. -/
theorem exists_computableInPolyTime_moduleLWEDecrypt :
    ∃ run : (((ℕ × ℕ) × ℕ) × List Bool × List Bool) → List Bool,
      ComputableInPolyTime run
        (encPair (encPair (encPair encUnary encUnary) encNat)
          (encPair encBits encBits)) encBits ∧
      ∀ (k n q : ℕ) (_hq : 0 < q)
        (s : Fin k → Fin n → ℤ)
        (ct : ModuleLWECiphertext k n q),
        run (((k, n), q), (ModuleSIS.encodeVec s,
          SIS.encodeMatrix (extendCiphertext ct))) =
          List.ofFn (moduleLWEDecrypt (fun j i => (s j i : ZMod q)) ct) :=
  ⟨decryptWords, decryptWords_polyTime, fun _ _ _ hq s ct => decryptWords_encode hq s ct⟩

/-! ### Total execution on off-canonical, zero-modulus and malformed inputs -/

/-- At modulus zero, the total runtime function remains defined, producing `false` for every
output bit without asserting quotient-ring semantics. -/
example : decryptWords (((1, 2), 0), ([], [])) = [false, false] := by
  simp only [decryptWords, Decoder.list, frames_nil, List.map_nil]
  decide

/-- Empty ciphertext and secret words are total: missing rows and coefficients pad with default
values, yielding a total boolean list of length `n`. -/
example : decryptWords (((2, 3), 29), ([], [])) = [false, false, false] := by
  simp only [decryptWords, Decoder.list, frames_nil, List.map_nil]
  decide

/-- Excess rows and secret entries are ignored while charging complete input length: a secret
list with 4 entries when only `k * n = 2` are needed, and a ciphertext matrix with 3 rows when
only `k + 1 = 2` are needed. -/
example :
    decryptWords (((1, 2), 29),
      (encList encIntBin [1, -1, 5, 10],
        encList (encList encNat) [[7, 8], [3, 4], [99, 100]])) =
      [false, false] := by
  simp only [decryptWords, Decoder.decode_enc]
  decide

/-- Incomplete framing and malformed words do not crash: raw bitstreams with irregular frame
delimiters decode via total fallbacks and produce valid output lists of length `n`. -/
example : (frames [true]).map decodeIntBin = [0] := by
  simp [frames, unframe, dropFrame, decodeIntBin, Decoder.nat, ofBits]

example :
    decryptWords (((1, 2), 29), ([true], [true])) = [false, false] := by
  have hf : frames [true] = [[]] := by
    rw [frames_of_ne_nil (by decide)]
    simp [unframe, dropFrame]
  have hs : (Decoder.list Decoder.intBin).decode [true] = [0] := by
    simp [Decoder.list, Decoder.intBin, hf, decodeIntBin, Decoder.nat, ofBits]
  have hct : (Decoder.list (Decoder.list Decoder.nat)).decode [true] = [[]] := by
    simp [Decoder.list, hf]
  simp only [decryptWords, hs, hct]
  decide

end Cslib.Crypto
