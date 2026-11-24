/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Crypto.Computational.ElGamal.KDF
import CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation
import CslibFrontier.Crypto.Computational.PseudorandomPermutation
import CslibFrontier.Crypto.Computational.PseudorandomPermutation.StrongSwitching
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime
import Mathlib.NumberTheory.Bertrand

set_option linter.privateModule false

/-!
# Checked non-vacuity witnesses for `LinearHashKDFConditions` and `BlockCipher.StrongPRP`

Ordinary `module` client (no `import all`) supplying missing witness checks from the crypto
non-vacuity audit:

1. **`PrimeOrderGroupFamily.LinearHashKDFConditions` (`ElGamal/KDF.lean`):** constructs a concrete
   additive prime-order group family `additivePrimeGroups` (`Carrier q = ZMod q` for prime `q`),
   discharges all five fields of `LinearHashKDFConditions` unconditionally for growing key length
   `msgLen n = n + 1` via Bertrand's postulate (`linearHashKDFConditions_bertrand`), instantiates
   `secureKDF_linearHashKDF` and `KeyDerivation.Secure` with no remaining hypotheses, and refutes
   `LinearHashKDFConditions` on a fixed group of order `2` (`not_linearHashKDFConditions_fixedTwo`).
2. **`BlockCipher.StrongPRP` (`PseudorandomPermutation.lean`):** refutes `idBlockCipher.StrongPRP`
   directly via a 1-query decryption-channel adversary `decryptZeroDistinguisher`
   (`not_strongPRP_idBlockCipher`), exercising `strongPRPRealGame`, `strongPRPIdealGame`, and
   `advantage_strongPRPIdealGame_forgetful_le` at `Q = 1`.
-/

namespace CslibFrontierTests.Crypto.KDFAndStrongPRPNonvacuity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### 1. `LinearHashKDFConditions`: concrete group family, satisfying & failing instances -/

section LinearHashKDF

/-- Description of an additive cyclic prime-order group: a prime natural number `q`. -/
private abbrev PrimeDesc : Type := { q : ℕ // q.Prime }

private def encPrimeDesc : PrimeDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans encNat

private theorem computableInPolyTime_primeDesc_val :
    ComputableInPolyTime (Subtype.val : PrimeDesc → ℕ) encPrimeDesc encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Additive prime-order cyclic groups `(ZMod q, +)` with generator `1` and little-endian binary
residue encoding `x.val.bits`. -/
def additivePrimeGroups : PrimeOrderGroupFamily where
  Desc := PrimeDesc
  encDesc := encPrimeDesc
  order d := d.val
  prime_order d := d.2
  Carrier d := ZMod d.val
  generator _ := 1
  card_carrier d := Nat.card_zmod d.val
  generator_ne_zero d := fun h => by
    have hval := congrArg ZMod.val h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt d.2.one_lt, ZMod.val_zero] at hval
    exact one_ne_zero hval
  encode _ x := x.val.bits
  encode_injective d _ _ h := @ZMod.val_injective d.val ⟨d.2.ne_zero⟩ _ _ (encNat.injective h)
  add | (d, x, y) => ((ofBits x + ofBits y) % d.val).bits
  add_encode d x y := by
    simp only [ofBits_bits]
    exact (congrArg Nat.bits (@ZMod.val_add d.val ⟨d.2.ne_zero⟩ x y)).symm
  smul | (d, a, x) => ((a * ofBits x) % d.val).bits
  smul_encode d a x := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    simp only [ofBits_bits]
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  computableInPolyTime_order := computableInPolyTime_primeDesc_val
  computableInPolyTime_generator := by
    have hconst : ComputableInPolyTime (fun _ : PrimeDesc => ([true] : List Bool))
        encPrimeDesc encBits :=
      ComputableInPolyTime.const [true]
    exact hconst.of_enc_eq fun d => by
      have : Fact (1 < d.val) := ⟨d.2.one_lt⟩
      rw [ZMod.val_one]
      rfl
  computableInPolyTime_add := by
    have hp := ComputableInPolyTime.id'
      (encIn := encDescBitsPair encPrimeDesc)
    have hd := computableInPolyTime_primeDesc_val.comp hp.fst'
    have hx := ComputableInPolyTime.bitsToNat.comp hp.snd'.fst'
    have hy := ComputableInPolyTime.bitsToNat.comp hp.snd'.snd'
    simpa only [encNat_apply, Function.comp_def] using
      (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_add' hx hy) hd).encoding_comp
  computableInPolyTime_smul := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair encPrimeDesc (encPair encNat encBits))
    have hd := computableInPolyTime_primeDesc_val.comp hp.fst'
    have ha := hp.snd'.fst'
    have hx := ComputableInPolyTime.bitsToNat.comp hp.snd'.snd'
    simpa only [encNat_apply, Function.comp_def] using
      (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.binary_mul' ha hx) hd).encoding_comp

private theorem exists_prime_between_two_pow (n : ℕ) :
    ∃ q : ℕ, q.Prime ∧ 2 ^ (2 * n + 1) < q ∧ q ≤ 2 ^ (2 * n + 2) := by
  obtain ⟨q, hqp, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (2 ^ (2 * n + 1)) (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨q, hqp, hlt, ?_⟩
  simpa only [Nat.pow_succ, mul_comm] using hle

/-- Prime description chosen in `(2 ^ (2 * n + 1), 2 ^ (2 * n + 2)]` via Bertrand's postulate. -/
noncomputable def bertrandPrimeDesc (n : ℕ) : additivePrimeGroups.Desc :=
  ⟨Classical.choose (exists_prime_between_two_pow n),
    (Classical.choose_spec (exists_prime_between_two_pow n)).1⟩

private theorem two_pow_lt_bertrandPrimeDesc (n : ℕ) :
    2 ^ (2 * n + 1) < (bertrandPrimeDesc n).val :=
  (Classical.choose_spec (exists_prime_between_two_pow n)).2.1

private theorem bertrandPrimeDesc_lt_two_pow (n : ℕ) :
    (bertrandPrimeDesc n).val < 2 ^ (2 * n + 2) := by
  have hspec := Classical.choose_spec (exists_prime_between_two_pow n)
  have hle : (bertrandPrimeDesc n).val ≤ 2 ^ (2 * n + 2) := hspec.2.2
  refine lt_of_le_of_ne hle fun heq => ?_
  have hp : (2 ^ (2 * n + 2)).Prime := heq ▸ hspec.1
  have hgt : 2 < 2 ^ (2 * n + 2) := by
    have : 2 ^ 1 < 2 ^ (2 * n + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simpa only [pow_one] using this
  have hdvd : 2 ∣ 2 ^ (2 * n + 2) := dvd_pow_self 2 (by omega)
  exact absurd (hp.eq_one_or_self_of_dvd 2 hdvd) (by omega)

private theorem bits_length_bertrandPrimeDesc (n : ℕ) :
    (bertrandPrimeDesc n).val.bits.length = 2 * n + 2 := by
  have hle : (bertrandPrimeDesc n).val.size ≤ 2 * n + 2 :=
    Nat.size_le.mpr (bertrandPrimeDesc_lt_two_pow n)
  have hlt : 2 * n + 1 < (bertrandPrimeDesc n).val.size :=
    Nat.lt_size.mpr (Nat.le_of_lt (two_pow_lt_bertrandPrimeDesc n))
  rw [← encNat_apply, length_encNat_eq_size]
  omega

/-- Deterministic growing-prime setup law using `bertrandPrimeDesc`. -/
noncomputable def bertrandSetup (n : ℕ) : PMF additivePrimeGroups.Desc :=
  PMF.pure (bertrandPrimeDesc n)

/-- Output key length computed from a group description: half the binary length of its order. -/
def halfOrderBitsLen (d : additivePrimeGroups.Desc) : ℕ :=
  (additivePrimeGroups.encDesc d).length / 2

/-- Encoding length bound computed from a group description: the binary length of its order. -/
def orderBitsBound (d : additivePrimeGroups.Desc) : ℕ :=
  (additivePrimeGroups.encDesc d).length

private theorem computableInPolyTime_halfOrderBitsLen :
    ComputableInPolyTime halfOrderBitsLen additivePrimeGroups.encDesc encUnary := by
  unfold halfOrderBitsLen
  exact (ComputableInPolyTime.unary_div_const 2).comp
    (ComputableInPolyTime.encoding_length additivePrimeGroups.encDesc)

private theorem computableInPolyTime_orderBitsBound :
    ComputableInPolyTime orderBitsBound additivePrimeGroups.encDesc encUnary := by
  unfold orderBitsBound
  exact ComputableInPolyTime.encoding_length additivePrimeGroups.encDesc

/-- Concrete satisfying instance of `PrimeOrderGroupFamily.LinearHashKDFConditions` with
growing output length `msgLen n = n + 1` and group order exceeding `2 ^ (2 * n + 1)`. -/
theorem linearHashKDFConditions_bertrand :
    additivePrimeGroups.LinearHashKDFConditions bertrandSetup halfOrderBitsLen orderBitsBound
      (fun n => n + 1) (fun n => 2 ^ (2 * n + 1)) where
  qMin_pos _ := Nat.two_pow_pos _
  keyLen_eq n d hd := by
    simp only [bertrandSetup, PMF.support_pure, Set.mem_singleton_iff] at hd
    subst hd
    change (encNat (bertrandPrimeDesc n).val).length / 2 = n + 1
    rw [encNat_apply, bits_length_bertrandPrimeDesc]
    omega
  length_encode_le _ d _ x := by
    have : NeZero d.val := ⟨d.2.ne_zero⟩
    change (encNat x.val).length ≤ (encNat d.val).length
    exact length_encNat_mono (Nat.le_of_lt x.val_lt)
  qMin_le_order n d hd := by
    simp only [bertrandSetup, PMF.support_pure, Set.mem_singleton_iff] at hd
    subst hd
    exact Nat.le_of_lt (two_pow_lt_bertrandPrimeDesc n)
  negligible := by
    have hfun : (fun n => (2 : ℝ≥0) ^ (n + 1) / ((2 ^ (2 * n + 1) : ℕ) : ℝ≥0)) =
        fun n => (2 ^ n : ℝ≥0)⁻¹ := by
      funext n
      push_cast
      have hpow : (2 : ℝ≥0) ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [hpow, div_mul_eq_div_div, div_self (pow_ne_zero _ two_ne_zero), one_div]
    rw [hfun]
    exact negligible_inv_two_pow

/-- Unconditional `SecureKDF` instantiation for positive growing output length `n + 1`, with all
hypotheses of `LinearHashKDFConditions` discharged. -/
theorem secureKDF_additivePrimeGroups_bertrand :
    additivePrimeGroups.withSeed.SecureKDF
      (additivePrimeGroups.seededSetup bertrandSetup
        (additivePrimeGroups.linearHashSeedLen (fun n => n + 1) orderBitsBound))
      (additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound)
      (fun n => n + 1) :=
  additivePrimeGroups.secureKDF_linearHashKDF linearHashKDFConditions_bertrand

/-- The linear-hash KDF over `additivePrimeGroups` is executable in polynomial time and is an
unconditional `KeyDerivation.Secure` instance via `secureKDF_iff_keyDerivation`. -/
theorem keyDerivation_secure_additivePrimeGroups :
    ComputableInPolyTime
        (additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound)
        (encPair additivePrimeGroups.withSeed.encDesc encBits) encBits ∧
      KeyDerivation.Secure additivePrimeGroups.withSeed.encCDHInput encBits
        (additivePrimeGroups.withSeed.kdfSecret
          (additivePrimeGroups.seededSetup bertrandSetup
            (additivePrimeGroups.linearHashSeedLen (fun n => n + 1) orderBitsBound)))
        PrimeOrderGroupFamily.DDHInput.toCDHInput
        (fun x => additivePrimeGroups.linearHashKDF halfOrderBitsLen orderBitsBound
          (x.groupParameters,
            additivePrimeGroups.withSeed.encode x.groupParameters x.candidateShared))
        (fun n => BitString.uniformList (n + 1)) :=
  ⟨additivePrimeGroups.computableInPolyTime_linearHashKDF
      computableInPolyTime_halfOrderBitsLen computableInPolyTime_orderBitsBound,
    (additivePrimeGroups.withSeed.secureKDF_iff_keyDerivation _ _ _).mp
      secureKDF_additivePrimeGroups_bertrand⟩

/-- Fixed group of order `2` in `additivePrimeGroups`. -/
private def fixedTwoDesc : additivePrimeGroups.Desc :=
  ⟨2, Nat.prime_two⟩

private theorem order_fixedTwoDesc : additivePrimeGroups.order fixedTwoDesc = 2 := rfl

/-- Negative witness: `LinearHashKDFConditions` fails when the group order remains fixed at `2`
with constant 1-bit output length, regardless of `keyLen`, `bound`, and `qMin`. -/
theorem not_linearHashKDFConditions_fixedTwo (keyLen _bound : additivePrimeGroups.Desc → ℕ)
    (qMin : ℕ → ℕ) :
    ¬ additivePrimeGroups.LinearHashKDFConditions
        (fun _ => PMF.pure fixedTwoDesc) keyLen _bound (fun _ => 1) qMin := by
  intro h
  have hle : ∀ n, (1 : ℝ≥0) ≤ (2 : ℝ≥0) ^ 1 / (qMin n : ℝ≥0) := fun n => by
    have hq_pos : (0 : ℝ≥0) < qMin n := Nat.cast_pos.mpr (h.qMin_pos n)
    have hq_le : qMin n ≤ 2 := by
      simpa only [order_fixedTwoDesc] using
        h.qMin_le_order n fixedTwoDesc (by simp only [PMF.support_pure, Set.mem_singleton_iff])
    rw [pow_one, one_le_div₀ hq_pos]
    exact_mod_cast hq_le
  exact not_negligible_const one_ne_zero (negligible_of_le h.negligible hle)

end LinearHashKDF

/-! ### 2. `BlockCipher.StrongPRP`: direct decryption-channel non-vacuity witness -/

section StrongPRP

/-- Identity block cipher on `(n + 1)`-bit keys and `(n + 1)`-bit blocks. -/
private def idBlockCipher : BlockCipher where
  keyLen n := n + 1
  blockLen n := n + 1
  keyLen_polyTime := by fun_prop
  blockLen_polyTime := by fun_prop
  encrypt _ _ block := block
  decrypt _ _ block := block
  encrypt_polyTime := by polytime
  decrypt_polyTime := by polytime
  length_encrypt _ _ _ _ hblock := hblock
  length_decrypt _ _ _ _ hblock := hblock
  decrypt_encrypt _ _ _ _ _ := rfl
  encrypt_decrypt _ _ _ _ _ := rfl

/-- One-query chosen-ciphertext distinguisher: sends a **decryption** query `(true, 0^(n+1))` and
checks whether the reply equals `0^(n+1)`. -/
private noncomputable def decryptZeroDistinguisher : StrongPRPDistinguisher := fun n _ => do
  let reply ← List.take (n + 1) <$> ProbOracleComp.query (true, List.replicate (n + 1) false)
  return reply == List.replicate (n + 1) false

private theorem isOraclePPT_decryptZeroDistinguisher :
    IsOraclePPT encBool decryptZeroDistinguisher := by
  have h : IsOraclePPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => decryptZeroDistinguisher p.1 p.2) := by
    ppt [decryptZeroDistinguisher]
  exact h.isOraclePPT

private theorem isQueryBounded_decryptZeroDistinguisher (n : ℕ) :
    (decryptZeroDistinguisher n []).IsQueryBounded 1 := by
  unfold decryptZeroDistinguisher
  refine OracleComp.IsCostBounded.bind (n := 1) (m := 0) ?_ fun _ => .pure _ 0
  rw [OracleComp.isCostBounded_map_iff]
  exact ProbOracleComp.IsQueryBounded.query _

private theorem eval_strongPRPRealGame_idBlockCipher_decryptZero (n : ℕ) :
    ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n) = PMF.pure true := by
  simp only [BlockCipher.strongPRPRealGame, decryptZeroDistinguisher, ProbOracleComp.run,
    idBlockCipher, BlockCipher.strongPRPOracle, List.length_replicate, ↓reduceIte,
    List.take_replicate, min_self, OracleComp.interpret_map, ProbOracleComp.interpret_query,
    map_pure, bind_pure_comp, ProbComp.eval_map, BitString.eval_sampleList, beq_self_eq_true]
  exact PMF.map_const _ _

private theorem succProbability_forgetful_decryptZero (n : ℕ) :
    Game.succProbability
        ((ProbOracleComp.runWith
          ((strongBitStringCodec (n + 1)).wordOracle RandomPermutation.forgetfulAnswer)
          (decryptZeroDistinguisher n []) []).map Prod.fst) =
      (2 ^ (n + 1) : ℝ≥0)⁻¹ := by
  have hword :
      (strongBitStringCodec (n + 1)).wordOracle RandomPermutation.forgetfulAnswer
        (true, List.replicate (n + 1) false) [] =
      (PMF.uniformOfFintype (BitString (n + 1))).map
        fun x => (List.ofFn x, [(x, BitString.ofList (n + 1) (List.replicate (n + 1) false))]) := by
    rw [strongBitStringCodec_wordOracle_of_length RandomPermutation.forgetfulAnswer true
      (word := List.replicate (n + 1) false) (List.length_replicate)]
    change ((RandomPermutation.forgetfulAnswer
      (RandomPermutation.PermQuery.inverse (BitString.ofList (n + 1) _))) []).map
        (fun p => (List.ofFn p.1, p.2)) = _
    rw [RandomPermutation.forgetfulAnswer_inverse_of_none rfl, PMF.map_comp]
    rfl
  have htake (x : BitString (n + 1)) :
      List.take (n + 1) (List.ofFn x) = List.ofFn x :=
    List.take_of_length_le (by simp only [List.length_ofFn, le_rfl])
  have hrun :
      ((ProbOracleComp.runWith
        ((strongBitStringCodec (n + 1)).wordOracle RandomPermutation.forgetfulAnswer)
        (decryptZeroDistinguisher n []) []).map Prod.fst) =
      (PMF.uniformOfFintype (BitString (n + 1))).map
        fun x => List.ofFn x == List.replicate (n + 1) false := by
    simp only [decryptZeroDistinguisher, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, hword, PMF.bind_map,
      PMF.map_bind, PMF.pure_map, Function.comp_def, Prod.map_fst, htake]
    exact (PMF.bind_pure_comp _ _).symm
  rw [hrun, Game.succProbability, PMF.map_apply]
  have hzero : ∀ x : BitString (n + 1),
      ((List.ofFn x == List.replicate (n + 1) false) = true) ↔ x = fun _ => false := by
    intro x
    rw [beq_iff_eq]
    constructor
    · intro hx
      funext i
      have hi := congrArg (fun l : List Bool => l[i.1]?) hx
      simp only [List.getElem?_ofFn, i.isLt, ↓reduceDIte, List.getElem?_replicate,
        ↓reduceIte, Option.some.injEq] at hi
      exact hi
    · intro hx
      subst hx
      simp only [List.ofFn_const]
  rw [tsum_eq_single (fun _ => false)]
  · have htrue : (List.ofFn (fun _ : Fin (n + 1) => false) == List.replicate (n + 1) false) =
        true := by
      simp only [List.ofFn_const, beq_self_eq_true]
    simp only [htrue, ↓reduceIte, PMF.uniformOfFintype_apply, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]
    push_cast
    rfl
  · intro x hx
    have hne : true ≠ (List.ofFn x == List.replicate (n + 1) false) :=
      Ne.symm ((hzero x).not.mpr hx)
    simp only [hne, ↓reduceIte]

/-- Direct decryption-channel refutation: `idBlockCipher` is not a `StrongPRP`. -/
theorem not_strongPRP_idBlockCipher : ¬ idBlockCipher.StrongPRP := by
  intro h
  have hneg := h decryptZeroDistinguisher isOraclePPT_decryptZeroDistinguisher
  have hle : ∀ n : ℕ, (1 / 2 : ℝ≥0) ≤
      Game.advantage
        (ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n))
        (ProbComp.eval (strongPRPIdealGame idBlockCipher.blockLen decryptZeroDistinguisher n)) := by
    intro n
    have hid := advantage_strongPRPIdealGame_forgetful_le idBlockCipher.blockLen
      decryptZeroDistinguisher n 1 (isQueryBounded_decryptZeroDistinguisher n)
    have hchoose : ((1 : ℕ).choose 2 : ℝ) = 0 := by norm_num
    rw [hchoose, zero_mul] at hid
    change (Game.advantage
      (ProbComp.eval (strongPRPIdealGame (fun n => n + 1) decryptZeroDistinguisher n))
      ((ProbOracleComp.runWith
        ((strongBitStringCodec (n + 1)).wordOracle RandomPermutation.forgetfulAnswer)
        (decryptZeroDistinguisher n []) []).map Prod.fst) : ℝ) ≤ 0 at hid
    have hsucc_ideal :
        Game.succProbability
          (ProbComp.eval (strongPRPIdealGame idBlockCipher.blockLen decryptZeroDistinguisher n)) ≤
          (2 ^ (n + 1) : ℝ≥0)⁻¹ := by
      have hc := Game.coe_succProbability_le_add_of_advantage_le hid
      rw [succProbability_forgetful_decryptZero, add_zero] at hc
      exact_mod_cast hc
    have hpow : (2 ^ (n + 1) : ℝ≥0)⁻¹ ≤ 1 / 2 := by
      rw [one_div, inv_le_inv₀ (pow_pos two_pos _) two_pos]
      exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero n) 2
    have htri := Game.advantage_triangle
      (ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n))
      (ProbComp.eval (strongPRPIdealGame idBlockCipher.blockLen decryptZeroDistinguisher n))
      (PMF.pure false)
    have hpure : Game.succProbability (PMF.pure true) = 1 := by simp [Game.succProbability]
    rw [Game.advantage_pure_false, Game.advantage_pure_false] at htri
    have hreal : Game.succProbability
        (ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n)) = 1 := by
      rw [eval_strongPRPRealGame_idBlockCipher_decryptZero, hpure]
    rw [hreal] at htri
    have htriR : (1 : ℝ) ≤ (Game.advantage
        (ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n))
        (ProbComp.eval (strongPRPIdealGame idBlockCipher.blockLen
          decryptZeroDistinguisher n)) : ℝ) +
        (Game.succProbability (ProbComp.eval (strongPRPIdealGame
          idBlockCipher.blockLen decryptZeroDistinguisher n)) : ℝ) := by
      exact_mod_cast htri
    have hideal_le : (Game.succProbability (ProbComp.eval (strongPRPIdealGame
        idBlockCipher.blockLen decryptZeroDistinguisher n)) : ℝ) ≤ 1 / 2 := by
      exact_mod_cast hsucc_ideal.trans hpow
    have hadvR : (1 / 2 : ℝ) ≤ (Game.advantage
        (ProbComp.eval (idBlockCipher.strongPRPRealGame decryptZeroDistinguisher n))
        (ProbComp.eval (strongPRPIdealGame idBlockCipher.blockLen
          decryptZeroDistinguisher n)) : ℝ) := by
      linarith
    exact_mod_cast hadvR
  exact not_negligible_const (by norm_num) (negligible_of_le hneg hle)

end StrongPRP

end CslibFrontierTests.Crypto.KDFAndStrongPRPNonvacuity
