/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SharedSecretExpansion
-- Reads private `matrixSeed`, `generatedPair`, and unexposed `Xofs.sampleSecretExpansionViews`.
import all CslibFrontier.Crypto.Computational.MLDSA.SharedSecretExpansion
-- Reads private `publicDraw` and `runSigningProgram` from `PublicPairSigning`.
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
-- Reads private `plant_off` and `uniform_plant`, plus unexposed `Xofs.withKeySeedExpansion`.
import all CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import CslibFrontier.Crypto.Primitives.ByteString.Uniform

/-!
# Prediction of the private FIPS expansion inputs

[FIPS 204][NISTFIPS204], Algorithms 6 and 33, use 64 bytes of the key-generation SHAKE output
as the common prefix of the short-vector inputs. The pure-mode signing service can read one of
those inputs as a message representative only if the encoded public key hashes to that prefix.
The hash matches with probability at most 2⁻⁵¹² under the original coupled setup. After
refreshing the single key-generation row of the background oracle, the pair and the refreshed
SHAKE128 and SHAKE256 streams are jointly independent of the original seeds. At any chosen coherent
query by the adaptive public-pair forger, the measured address hits a private input with
probability at most 2⁻²⁵⁶. Both statements retain setup failure.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability
open scoped ENNReal

/-- Successful key generation produces a public-key hash equal to its own private Algorithm 33
prefix. This is the exceptional honest representative input in the shared-row comparison. -/
def SecretExpansionViews.publicHashMatch {s : Level} (v : SecretExpansionViews s) : Bool :=
  v.pair.any fun pk => v.shared.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64 ==
    v.secretSeed.toList

/-- The native and detached devices return the same public-key hash, at every read length. -/
theorem SecretExpansionViews.read_publicKey_of_mem {s : Level} {base : Xofs} {a b : ℕ}
    {ha : 528 ≤ a} {hb : 481 ≤ b} {v : SecretExpansionViews s}
    (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support) (t : Fin s.params.k → Poly)
    (n : ℕ) : v.shared.h256.readBytes (encodePublic s v.publicSeed.toList t) n =
      v.background.h256.readBytes (encodePublic s v.publicSeed.toList t) n := by
  refine ExtendableOutput.read_eq_of_byteAt_eq fun i _ =>
    (agree_of_mem hv).2 _ i (Or.inr fun j e => ?_)
  have h := congrArg List.length e
  rw [Keccak.length_bytesToBitsLE, length_encodePublic, FixedBytes.length_toList,
    length_nonceInput_bits] at h
  cases s <;> contradiction

/-- On successful setup, the honest empty request reads nonce zero exactly when the
native public-key hash matches the private prefix. -/
theorem SecretExpansionViews.publicHashMatch_iff {s : Level} {v : SecretExpansionViews s}
    {pk : MLDSA.PublicKey s.params} (hp : v.pair = some pk) :
    v.publicHashMatch ↔
      representativeInput (v.shared.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64)
        (formatMessage [] []) = Keccak.bytesToBitsLE (nonceInput v.secretSeed.toList 0) := by
  let tr := v.shared.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64
  obtain ⟨t, ht⟩ := FixedBytes.exists_toList (show tr.length = 64 from v.shared.h256.length_read ..)
  simp only [publicHashMatch, hp, Option.any_some, beq_iff_eq]
  change tr = v.secretSeed.toList ↔ representativeInput tr _ = _
  rw [← ht]
  simpa only [Fin.val_zero, and_self, and_true, FixedBytes.toList, List.ofFn_inj] using
    (representativeInput_eq_nonceInput_iff t v.secretSeed [] [] (0 : Fin 65536)).symm

private theorem replace_expansion (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (x y : FixedBytes 128) :
    (H.withKeySeedExpansion s seed x).withKeySeedExpansion s seed y =
      H.withKeySeedExpansion s seed y := by
  refine congrArg (Xofs.mk H.h128) (ExtendableOutput.ext_byteAt fun word i => ?_)
  simp only [Xofs.withKeySeedExpansion, ExtendableOutput.byteAt_withPrefixes]
  by_cases h : word = keySeedInput s seed
  · simp only [h, ↓reduceIte, Option.bind_some, FixedBytes.toList, List.getElem?_ofFn]
    split <;> rfl
  · simp [h]

private abbrev SeedScore (s : Level) (α : Type) :=
  Xofs → FixedBytes 32 → Option (MLDSA.PublicKey s.params) → FixedBytes 32 → FixedBytes 64 → PMF α

private def gen {s : Level} (H : Xofs) (rho : FixedBytes 32) (rows : Nonce s × Fin 481 → Byte) :=
  generatedPair (H.expandA s rho.toList) (vectors s (rowPair s rows))

private noncomputable def scoreRefresh {s : Level} {α : Type} (H : Xofs) (seed : FixedBytes 32)
    (rows : Nonce s × Fin 481 → Byte) (score : SeedScore s α) : PMF α :=
  let rho := matrixSeed H s seed
  (PMF.uniformOfFintype (FixedBytes 128)).bind fun fresh =>
    score (H.withKeySeedExpansion s seed fresh) rho (gen H rho rows) seed (expansionSeed H s seed)

private theorem score_programmed {s : Level} {α : Type} (H : Xofs) (xi rho : FixedBytes 32)
    (r : FixedBytes 64) (K : FixedBytes 32) (rows : Nonce s × Fin 481 → Byte)
    (score : SeedScore s α) :
    scoreRefresh (H.withKeySeedExpansion s xi (Fin.append rho (Fin.append r K))) xi rows score =
      (PMF.uniformOfFintype (FixedBytes 128)).bind fun fresh =>
        score (H.withKeySeedExpansion s xi fresh) rho (gen H rho rows) xi r := by
  let F := H.withKeySeedExpansion s xi (Fin.append rho (Fin.append r K))
  have ex : F.expandKeySeed s xi = rho.toList ++ (r.toList ++ K.toList) := by
    simp only [F, Xofs.expandKeySeed_withKeySeedExpansion, FixedBytes.toList, List.ofFn_fin_append]
  have pub : matrixSeed F s xi = rho := List.ofFn_inj.mp <| by
    change (matrixSeed F s xi).toList = rho.toList
    rw [matrixSeed_bytes, ex, List.take_left' (FixedBytes.length_toList rho)]
  have sec : expansionSeed F s xi = r := List.ofFn_inj.mp <| by
    change (expansionSeed F s xi).toList = r.toList
    rw [expansionSeed_bytes, ex, List.drop_left' (FixedBytes.length_toList rho),
      List.take_left' (FixedBytes.length_toList r)]
  change (PMF.uniformOfFintype (FixedBytes 128)).bind (fun fresh =>
    score (F.withKeySeedExpansion s xi fresh) _ _ xi _) = _
  rw [pub, sec]
  simp only [F, replace_expansion]; rfl

private theorem refresh_fixed {s : Level} {α : Type} (base : Xofs) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 128 ≤ b) (xi : FixedBytes 32) (rows : Nonce s × Fin 481 → Byte)
    (score : SeedScore s α) :
    ((base.uniformPrefixes a b).bind fun H => scoreRefresh H xi rows score) =
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun rho =>
        (PMF.uniformOfFintype (FixedBytes 64)).bind fun r =>
          (base.uniformPrefixes a b).bind fun H => score H rho (gen H rho rows) xi r := by
  let R := base.uniformPrefixes a b
  let P := PMF.uniformOfFintype (FixedBytes 32)
  let U := PMF.uniformOfFintype (FixedBytes 64)
  let B := PMF.uniformOfFintype (FixedBytes 128)
  rw [← uniform_plant base s xi ha hb (fun H => scoreRefresh H xi rows score)]
  have each (H : Xofs) :
      (B.bind fun out => scoreRefresh (H.withKeySeedExpansion s xi out) xi rows score) =
        P.bind fun rho => U.bind fun r => B.bind fun fresh =>
          score (H.withKeySeedExpansion s xi fresh) rho (gen H rho rows) xi r := by
    rw [← PMF.uniformOfFintype_bind_bind_equiv (Fin.appendEquiv 32 96 (α := Byte))]
    refine congrArg (PMF.bind P ·) (funext fun rho => ?_)
    rw [← PMF.uniformOfFintype_bind_bind_equiv (Fin.appendEquiv 64 32 (α := Byte))]
    simp only [Fin.appendEquiv, Equiv.coe_fn_mk, score_programmed, PMF.bind_const, U, B]
  change (R.bind fun H => B.bind fun out => _) = _
  simp_rw [each]
  rw [PMF.bind_comm R P]
  refine congrArg (PMF.bind P ·) (funext fun rho => ?_)
  rw [PMF.bind_comm R U]
  exact congrArg (PMF.bind U ·) (funext fun r =>
    uniform_plant base s xi ha hb (fun H => score H rho (gen H rho rows) xi r))

/-- Replace the 128 bytes at the input which generated both seeds, preserving every other
SHAKE response and the suffix at that input. The key pair has already been drawn. -/
noncomputable def SecretExpansionViews.refreshKeySeed {s : Level} (v : SecretExpansionViews s) :
    PMF Xofs :=
  (PMF.uniformOfFintype (FixedBytes 128)).map fun fresh =>
    v.background.withKeySeedExpansion s v.keySeed fresh

private theorem refresh_law {s : Level} {α : Type} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) (score : SeedScore s α) :
    ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      score H v.publicSeed v.pair v.keySeed v.secretSeed) =
    (PMF.uniformOfFintype (FixedBytes 32)).bind fun xi =>
      (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).bind fun rows =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun rho =>
      (PMF.uniformOfFintype (FixedBytes 64)).bind fun r =>
      (base.uniformPrefixes a b).bind fun H => score H rho (gen H rho rows) xi r := by
  let S := PMF.uniformOfFintype (FixedBytes 32)
  let V := PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)
  let R := base.uniformPrefixes a b
  have avg : ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      score H v.publicSeed v.pair v.keySeed v.secretSeed) =
      R.bind fun H => S.bind fun xi => V.bind fun rows => scoreRefresh H xi rows score := by
    simp only [Xofs.sampleSecretExpansionViews, SecretExpansionViews.refreshKeySeed, PMF.bind_bind,
      PMF.bind_map, Function.comp_def, R, independent_tables, scoreRefresh, gen, matrixSeed_bytes]
    rfl
  rw [avg, PMF.bind_comm R S]
  simp_rw [PMF.bind_comm R V]
  simp only [R, S, V, refresh_fixed base ((by decide : 272 ≤ 528).trans ha)
    ((by decide : 128 ≤ 481).trans hb)]

private theorem independent_law {s : Level} {α : Type} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) (score : SeedScore s α) :
    ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      score H v.publicSeed v.pair v.keySeed v.secretSeed) =
    (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).bind fun rows =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun rho =>
      (base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun xi =>
      (PMF.uniformOfFintype (FixedBytes 64)).bind fun r => score H rho (gen H rho rows) xi r := by
  let P := PMF.uniformOfFintype (FixedBytes 32)
  let U := PMF.uniformOfFintype (FixedBytes 64)
  let V := PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)
  let R := base.uniformPrefixes a b
  rw [refresh_law base ha hb, PMF.bind_comm P V]
  refine congrArg (PMF.bind V ·) (funext fun rows => ?_)
  rw [PMF.bind_comm P P]
  refine congrArg (PMF.bind P ·) (funext fun rho => ?_)
  change (P.bind fun xi => U.bind fun r => R.bind fun H => _) = _
  simp_rw [PMF.bind_comm U R]
  rw [PMF.bind_comm P R]

/-- After refreshing the 128-byte key-generation row of the background device, the original
32-byte key seed and 64-byte secret-expansion seed are independent uniform values jointly with
the full pair, published seed and complete refreshed XOFs. The observation can continue with
arbitrary signing and quantum interactions on that device. -/
theorem Xofs.refreshKeySeed_independent {s : Level} {α : Type} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b)
    (observe : Xofs → FixedBytes 32 → Option (MLDSA.PublicKey s.params) →
      FixedBytes 32 → FixedBytes 64 → PMF α) :
    let V := base.sampleSecretExpansionViews s ha hb
    (V.bind fun v => v.refreshKeySeed.bind fun H =>
      observe H v.publicSeed v.pair v.keySeed v.secretSeed) =
    (V.bind fun v => v.refreshKeySeed.bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun xi =>
      (PMF.uniformOfFintype (FixedBytes 64)).bind fun r => observe H v.publicSeed v.pair xi r) := by
  intro V
  let observe' : SeedScore s α := fun H rho pair _ _ =>
    (PMF.uniformOfFintype (FixedBytes 32)).bind fun xi =>
      (PMF.uniformOfFintype (FixedBytes 64)).bind fun r => observe H rho pair xi r
  change _ = V.bind fun v => v.refreshKeySeed.bind fun H =>
    observe' H v.publicSeed v.pair v.keySeed v.secretSeed
  rw [independent_law base ha hb observe, independent_law base ha hb observe']
  simp only [observe', PMF.bind_const]


/-- The FIPS public-key hash hits the private secret-expansion prefix with probability at
most 2⁻⁵¹² at every level. This bounds the exceptional honest representative for all requests
together. Failed matrix or secret expansion scores zero. -/
theorem publicHashMatch_le (s : Level) (base : Xofs) {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) :
    ((base.sampleSecretExpansionViews s ha hb).map (·.publicHashMatch)) true ≤
      (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  let test : SeedScore s Bool := fun H rho pair _ r => PMF.pure (pair.any fun pk =>
    H.h256.readBytes (encodePublic s rho.toList pk.t) 64 == r.toList)
  let V := base.sampleSecretExpansionViews s ha hb
  have keep (v : SecretExpansionViews s) (hv : v ∈ V.support) :
      v.refreshKeySeed.bind (fun H => test H v.publicSeed v.pair v.keySeed v.secretSeed) =
      PMF.pure v.publicHashMatch := by
    have read (fresh : FixedBytes 128) (pk : MLDSA.PublicKey s.params) :
        (v.background.withKeySeedExpansion s v.keySeed fresh).h256.readBytes
          (encodePublic s v.publicSeed.toList pk.t) 64 =
        v.background.h256.readBytes (encodePublic s v.publicSeed.toList pk.t) 64 := by
      apply plant_off
      rw [Keccak.length_bytesToBitsLE, length_encodePublic, FixedBytes.length_toList]
      cases s <;> decide
    simp only [SecretExpansionViews.refreshKeySeed, PMF.bind_map, Function.comp_def, test, read,
      PMF.bind_const, SecretExpansionViews.publicHashMatch, v.read_publicKey_of_mem hv]
  change ((base.sampleSecretExpansionViews s ha hb).bind fun v =>
    PMF.pure v.publicHashMatch) true ≤ _
  rw [PMF.bind_congr_on_support V _ _ (fun v hv => (keep v hv).symm),
    base.refreshKeySeed_independent ha hb test]
  refine PMF.bind_apply_le_on_support _ fun v _ => PMF.bind_apply_le_on_support _ fun H _ => ?_
  simp only [test, PMF.bind_const]
  refine FixedBytes.uniform_test_le (n := 64) fun x hx y hy => ?_
  cases hp : v.pair with
  | none => simp [hp] at hx
  | some pk =>
    simp only [Set.mem_ofPred_eq, hp, Option.any_some, beq_iff_eq] at hx hy
    exact List.ofFn_inj.mp (hx.symm.trans hy)

/-- A raw SHAKE256 address hits the key-expansion input or one of the secret-vector inputs. -/
def hitsExpansionInput (s : Level) (key : FixedBytes 32) (secret : FixedBytes 64)
    (address : Option (List Bool)) : Bool :=
  address.any fun x => decide (x = keySeedInput s key ∨
    ∃ j : Fin (s.params.ℓ + s.params.k), x = Keccak.bytesToBitsLE (nonceInput secret.toList j.val))

private theorem uniform_hit_le (s : Level) (address : Option (List Bool)) :
    ((PMF.uniformOfFintype (FixedBytes 32)).bind fun xi =>
      (PMF.uniformOfFintype (FixedBytes 64)).map fun r => hitsExpansionInput s xi r address) true ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  cases address with
  | none => simp [hitsExpansionInput]
  | some x =>
    by_cases width : x.length = 272
    · simp_rw [PMF.map]
      rw [PMF.bind_comm]
      apply PMF.bind_apply_le_on_support
      intro r _
      refine FixedBytes.uniform_test_le (n := 32) fun i hi j hj => ?_
      have off (k : Fin (s.params.ℓ + s.params.k)) :
          x ≠ Keccak.bytesToBitsLE (nonceInput r.toList k.val) := fun h => by
        rw [h, length_nonceInput_bits] at width
        exact (by decide : (528 : ℕ) ≠ 272) width
      simp only [Set.mem_ofPred_eq, hitsExpansionInput, Option.any_some, decide_eq_true_eq,
        off, exists_false, or_false] at hi hj
      exact List.ofFn_inj.mp (List.append_cancel_right
        (Keccak.bytesToBitsLE_injective (hi.symm.trans hj)))
    · apply PMF.bind_apply_le_on_support
      intro xi _
      have off : x ≠ keySeedInput s xi := fun h => width (h ▸ length_keySeedInput s xi)
      refine (FixedBytes.uniform_test_le (n := 64) fun r hr t ht => ?_).trans
        (ENNReal.inv_le_inv.mpr
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            (by decide : 256 ≤ 8 * 64)))
      simp only [Set.mem_ofPred_eq, hitsExpansionInput, Option.any_some, decide_eq_true_eq,
        off, false_or] at hr ht
      obtain ⟨i, hi⟩ := hr
      obtain ⟨j, hj⟩ := ht
      have eq := congrArg (List.take 64) (Keccak.bytesToBitsLE_injective (hi.symm.trans hj))
      simp only [nonceInput, List.take_left' (FixedBytes.length_toList _)] at eq
      exact List.ofFn_inj.mp eq

/-- In the refreshed background experiment any observation producing one raw SHAKE256 address
hits either private expansion input family with probability at most 2⁻²⁵⁶. The observation sees
the whole refreshed oracle and generated pair; a missing query or failed key setup scores zero. -/
theorem Xofs.refreshKeySeed_queryHit_le {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b)
    (query : Xofs → FixedBytes 32 → MLDSA.PublicKey s.params → PMF (Option (List Bool))) :
    ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      match v.pair with
      | none => PMF.pure false
      | some pk => (query H v.publicSeed pk).map
          (hitsExpansionInput s v.keySeed v.secretSeed)) true ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let test : SeedScore s Bool := fun H rho pair xi r => match pair with
    | none => PMF.pure false
    | some pk => (query H rho pk).map (hitsExpansionInput s xi r)
  change ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
    test H v.publicSeed v.pair v.keySeed v.secretSeed) true ≤ _
  rw [base.refreshKeySeed_independent ha hb test]
  refine PMF.bind_apply_le_on_support _ fun v _ => PMF.bind_apply_le_on_support _ fun H _ => ?_
  cases h : v.pair with
  | none => simp [test]
  | some pk =>
    simp only [test, PMF.map]
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype (FixedBytes 64)) (query H v.publicSeed pk)]
    rw [PMF.bind_comm (PMF.uniformOfFintype (FixedBytes 32)) (query H v.publicSeed pk)]
    exact PMF.bind_apply_le_on_support _ fun q _ => uniform_hit_le s q

namespace QuantumSigningForger

-- The challenger retains earlier writes so it can compare the responses at the measured address.
private noncomputable def queryWrites (C : QuantumSigningForger) (s : Level) (j : ℕ)
    (H : Xofs) (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) :
    PMF (List (TerminalSigningWrite s) × Option (Address C)) :=
  let pk := encodePublic s rho.toList pair.t
  let p := queryPrefix (C := C) (C.program pk) j
  let run := C.runSigningProgram s H (H.h256.readBytes pk 64) (publicDraw s pair) p
  run.bind fun (found, dev, hist) =>
    (addressRead C (found, dev, hist.log)).map fun addr => (hist.writes, addr)

/-- Measure the address actually supplied to the selected coherent query of the public-pair
signing experiment. An absent query, SHAKE128 query or invalid padding returns `none`. -/
noncomputable def publicPairQueryAddress (C : QuantumSigningForger) (s : Level) (j : ℕ)
    (H : Xofs) (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) : PMF (Option (List Bool)) :=
  (C.queryWrites s j H rho pair).map fun x => Xofs.shake256QueryInput x.2

/-- At any chosen query of the adaptive public-pair signer with a refreshed key seed row,
the measured SHAKE256 address hits a private expansion input with probability at most 2⁻²⁵⁶. -/
theorem publicPairQueryHit_le (C : QuantumSigningForger) (s : Level) (j : ℕ) (base : Xofs)
    {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) :
    ((base.sampleSecretExpansionViews s ha hb).bind fun v => v.refreshKeySeed.bind fun H =>
      match v.pair with
      | none => PMF.pure false
      | some pk => (C.publicPairQueryAddress s j H v.publicSeed pk).map
          (hitsExpansionInput s v.keySeed v.secretSeed)) true ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  base.refreshKeySeed_queryHit_le ha hb (C.publicPairQueryAddress s j)

end QuantumSigningForger
end Cslib.Crypto.MLDSA.FIPS204
