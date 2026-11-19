/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.QueryDisturbance
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
import CslibFrontier.Probability.PMF.UniformPoint
import all CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr

/-!
# Private signing-seed prediction and the key-generation query

[FIPS 204][NISTFIPS204], Algorithm 6, line 1, expands the key-generation seed and the
two dimension bytes into 128 bytes. The last 32 bytes are the signing seed `K`.

`keySeedDeviceGame_true` identifies the original prediction experiment with one in which
only the quantum device can access that programmed input. Signing uses the independent
mask-seed rows of `signingSeedPredictionGame`, including its fallback after the tape of `n`
rows is exhausted. The background device predicts `K`
with probability at most `2 / 2^256` and encounters a changed response at each fixed query
with probability at most `1 / 2^256`. Before its first coherent query the original device
also satisfies the prediction bound, with arbitrary prior classical signing requests.

For any retained density matrix independent of the hidden input seed, the mean squared
amplitude displacement of one coherent query by the installed expansion is at most `4 / 2^256`.
The same bound holds for the mean square change in the square root of the acceptance probability
of any seed-dependent measurement after that query.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum ExtendableOutput
open scoped ENNReal

/-- Install the 128-byte Algorithm 6 expansion at its raw SHAKE256 input, preserving the suffix. -/
def Xofs.withKeySeedExpansion (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (out : FixedBytes 128) : Xofs :=
  { H with h256 := H.h256.withPrefixes fun x =>
      if x = keySeedInput s seed then some out.toList else none }

/-- Algorithm 6 reads precisely the installed expansion bytes. -/
theorem Xofs.expandKeySeed_withKeySeedExpansion (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (out : FixedBytes 128) :
    (H.withKeySeedExpansion s seed out).expandKeySeed s seed = out.toList := by
  change ((H.withKeySeedExpansion s seed out).h256.read (keySeedInput s seed) 128) = _
  simp [Xofs.withKeySeedExpansion, ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix,
    List.take_of_length_le (FixedBytes.length_toList out).le,
    List.drop_eq_nil_of_le (H.h256.length_read (keySeedInput s seed) 128).le]

private theorem plant_off (H : Xofs) (s : Level) (seed : FixedBytes 32) (out : FixedBytes 128)
    {x : List Bool} (h : x.length ≠ 272) (n : ℕ) :
    (H.withKeySeedExpansion s seed out).h256.read x n = H.h256.read x n := by
  have ne : x ≠ keySeedInput s seed := fun eq => h (eq ▸ length_keySeedInput s seed)
  simp [Xofs.withKeySeedExpansion, ExtendableOutput.withPrefixes, ne]

private theorem uniform_plant (base : Xofs) (s : Level) (seed : FixedBytes 32) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 128 ≤ b) {α : Type} (f : Xofs → PMF α) :
    ((base.uniformPrefixes a b).bind fun H => (PMF.uniformOfFintype (FixedBytes 128)).bind
      fun out => f (H.withKeySeedExpansion s seed out)) = (base.uniformPrefixes a b).bind f := by
  let x := keySeedInput s seed
  have hx : x.length ≤ a := (length_keySeedInput ..).le.trans ha
  let e (i : Fin 128) : RawWord a × Fin b := (word x hx, i.castLE hb)
  have he : Function.Injective e := fun _ _ eq => Fin.ext (congrArg (fun p => p.2.val) eq)
  have install_eq (U T : Table a b) (out : FixedBytes 128) :
      (streams base U T).withKeySeedExpansion s seed out =
        streams base U (Function.extend e out T) := by
    apply congrArg (Xofs.mk (install base.h128 U))
    apply ext_byteAt
    intro y i
    change byteAt ((install base.h256 T).withPrefixes _) y i = _
    rw [byteAt_withPrefixes]
    simp only [byteAt_install]
    by_cases same : y = x
    · subst y
      simp only [← show x = keySeedInput s seed from rfl, ↓reduceIte, Option.bind_some,
        FixedBytes.toList, List.getElem?_ofFn]
      by_cases hi : i < 128
      · have small := hi.trans_le hb
        simp only [hi, ↓reduceDIte, Option.getD_some, hx, small, and_self]
        exact (he.extend_apply out T ⟨i, hi⟩).symm
      · simp only [hi, ↓reduceDIte, Option.getD_none]
        split
        next h =>
          apply Eq.symm
          apply Function.extend_apply'
          rintro ⟨j, eq⟩
          exact hi ((congrArg (fun p => p.2.val) eq : j.val = i) ▸ j.isLt)
        next => rfl
    · have miss : y ≠ keySeedInput s seed := same
      simp only [miss, ↓reduceIte, Option.bind_none, Option.getD_none]
      split
      next h =>
        apply Eq.symm
        apply Function.extend_apply'
        rintro ⟨j, eq⟩
        exact same (word_inj (hx := hx) (hy := h.1) (congrArg Prod.fst eq)).symm
      next => rfl
  simp only [independent_tables, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Table a b)),
    PMF.bind_comm (PMF.uniformOfFintype (Table a b)) (PMF.uniformOfFintype (Table a b))
      (fun t u => f ⟨install base.h128 u, install base.h256 t⟩)]
  congr 1
  funext u
  change ((PMF.uniformOfFintype (Table a b)).bind fun t =>
    (PMF.uniformOfFintype (FixedBytes 128)).bind fun out =>
      f ((streams base u t).withKeySeedExpansion s seed out)) = _
  simp only [install_eq]
  exact PMF.uniformOfFintype_bind_bind_extend e (fun t => f (streams base u t))

private structure RowSigner where
  /-- The encoded key passed to the forger. -/
  publicKey : List Byte
  /-- The 64-byte SHAKE256 hash of the encoded public key. -/
  hash : List Byte
  /-- The complete FIPS retry loop with a private mask-seed row. -/
  reply : Row → SigningQuery → Option (List Byte)

private def rowSigner (H : Xofs) (s : Level) (seed : FixedBytes 32) : Option RowSigner :=
  (H.keyGen s seed).map fun k =>
    ⟨k.publicKey, H.h256.readBytes k.publicKey 64, fun row q => H.signWithRow s k.secretKey q row⟩

private theorem decode_rekey {s : Level} (sk : PrivateKey s) (rhoLen : sk.rho.length = 32)
    (keyLen : sk.key.length = 32) (trLen : sk.tr.length = 64) (K : FixedBytes 32) :
    decodePrivate s ({sk with key := K.toList} : PrivateKey s).encode =
      (decodePrivate s sk.encode).map fun v => { v with key := K.toList } := by
  unfold decodePrivate
  dsimp only
  rw [sk.length_encode rhoLen keyLen trLen,
    PrivateKey.length_encode {sk with key := K.toList} rhoLen (FixedBytes.length_toList K) trLen]
  simp only [guard,
    ↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
    PrivateKey.encode, List.drop_left' rhoLen, List.drop_left' keyLen,
    List.drop_left' (FixedBytes.length_toList K), List.take_left' rhoLen, List.take_left' keyLen,
    List.take_left' (FixedBytes.length_toList K), List.take_left' trLen, List.drop_left' trLen]

private theorem decoded_tr {s : Level} (sk v : PrivateKey s) (rhoLen : sk.rho.length = 32)
    (keyLen : sk.key.length = 32) (trLen : sk.tr.length = 64)
    (hv : decodePrivate s sk.encode = some v) : v.tr = sk.tr := by
  unfold decodePrivate at hv
  dsimp only at hv
  rw [sk.length_encode rhoLen keyLen trLen] at hv
  simp only [guard, ↓reduceIte,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hv
  rw [← hv]
  simp only [PrivateKey.encode, List.drop_left' rhoLen, List.drop_left' keyLen,
    List.take_left' trLen]

private abbrev signDecoded (H : Xofs) (s : Level) (m : List Bool) (r : Row) (v : PrivateKey s) :=
  H.runSigning s (H.startDecodedSigning s v m fun μ => (r (BitString.ofList 512 μ)).toList)

private theorem signDecoded_plant (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (out : FixedBytes 128) (K : FixedBytes 32) (v : PrivateKey s) (ht : v.tr.length = 64)
    (m : List Bool) (r : Row) :
    signDecoded (H.withKeySeedExpansion s seed out) s m r {v with key := K.toList} =
      signDecoded H s m r v := by
  let μ := H.representativeFromTr v.tr m
  have rep : (H.withKeySeedExpansion s seed out).representativeFromTr v.tr m = μ := by
    apply congrArg Keccak.bytesToBitsLE
    apply plant_off
    simp only [representativeInput, List.length_append, Keccak.length_bytesToBitsLE, ht]
    lia
  have hμ : μ.length = 512 := by
    simp [μ, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, H.h256.length_read]
  unfold signDecoded Xofs.runSigning Xofs.startDecodedSigning
  dsimp only
  rw [rep, Xofs.expandA_congr (H := H) (K := H.withKeySeedExpansion s seed out) rfl]
  cases H.expandA s v.rho with
  | none => simp only [Option.bind_eq_bind, Option.bind_none]
  | some A =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    apply congrArg (fun f => firstAccepted s.params.ℓ f 814 0)
    funext κ
    apply attempt_congr_of_read (s := s) (sk := v) (r := r (BitString.ofList 512 μ))
      (fun _ h => plant_off H s seed out h) (by decide) _ (by cases s <;> decide)
    intro w
    simp only [commitmentInput, List.length_append, hμ]
    lia

private theorem row_eq_decoded (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (r : Row) (hc : q.context.length ≤ 255) :
    H.signWithRow s sk q r =
      (decodePrivate s sk).bind (signDecoded H s (formatMessage q.message q.context) r) := by
  simp only [Xofs.signWithRow, hc, guard, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  unfold Xofs.startSigningWithSeed signDecoded
  cases decodePrivate s sk with
  | none => rfl
  | some v => rfl

private theorem bind_rekey {s : Level} (sk : PrivateKey s) (hr : sk.rho.length = 32)
    (hk : sk.key.length = 32) (ht : sk.tr.length = 64) (K : FixedBytes 32)
    {α : Type} (f g : PrivateKey s → Option α)
    (eq : ∀ v : PrivateKey s, v.tr.length = 64 → f {v with key := K.toList} = g v) :
    (decodePrivate s ({sk with key := K.toList} : PrivateKey s).encode).bind f =
      (decodePrivate s sk.encode).bind g := by
  rw [decode_rekey sk hr hk ht K]
  cases hv : decodePrivate s sk.encode with
  | none => rfl
  | some v => exact eq v ((decoded_tr sk v hr hk ht hv) ▸ ht)

private theorem sign_plant (H : Xofs) (s : Level) (seed : FixedBytes 32) (out : FixedBytes 128)
    (sk : PrivateKey s) (hr : sk.rho.length = 32) (hk : sk.key.length = 32)
    (ht : sk.tr.length = 64) (K : FixedBytes 32) (q : SigningQuery) (r : Row) :
    (H.withKeySeedExpansion s seed out).signWithRow s
      ({sk with key := K.toList} : PrivateKey s).encode q r = H.signWithRow s sk.encode q r := by
  by_cases ctx : q.context.length ≤ 255
  · rw [row_eq_decoded _ _ _ _ _ ctx, row_eq_decoded _ _ _ _ _ ctx]
    exact bind_rekey sk hr hk ht K _ _ fun v hv => signDecoded_plant H s seed out K v hv _ r
  · simp [Xofs.signWithRow, ctx, guard]

private def setupOracle (H : Xofs) (s : Level) (p : FixedBytes 96) :=
  H.withKeySeedExpansion s (fun _ => 0) (Fin.append p (fun _ : Fin 32 => 0))

private theorem rowSigner_plant (H : Xofs) (s : Level) (p : FixedBytes 96)
    (seed K : FixedBytes 32) :
    rowSigner (H.withKeySeedExpansion s seed (Fin.append p K)) s seed =
      rowSigner (setupOracle H s p) s (fun _ => 0) := by
  let z : FixedBytes 32 := fun _ => 0
  let rho := p.toList.take 32
  let rho' := p.toList.drop 32
  have rh : rho.length = 32 := by simp [rho]
  have rh' : rho'.length = 64 := by simp [rho']
  have fields (t : FixedBytes 32) :
      ((FixedBytes.toList (n := 128) (Fin.append p t)).take 32 = rho) ∧
      (((FixedBytes.toList (n := 128) (Fin.append p t)).drop 32).take 64 = rho') ∧
      ((FixedBytes.toList (n := 128) (Fin.append p t)).drop 96 = t.toList) := by
    rw [show FixedBytes.toList (n := 128) (Fin.append p t) = p.toList ++ t.toList from
      List.ofFn_fin_append p t]
    simp only [rho, rho', List.take_append, List.drop_append, FixedBytes.length_toList,
      List.take_left' rh',
      List.drop_left' (FixedBytes.length_toList p)]
    simp
  let G (seed K : FixedBytes 32) := H.withKeySeedExpansion s seed (Fin.append p K)
  have short seed K i : (G seed K).secretPoly s rho' i = H.secretPoly s rho' i := by
    unfold Xofs.secretPoly
    rw [show (G seed K).h256.readBytes (nonceInput rho' i) 481 =
          H.h256.readBytes (nonceInput rho' i) 481 from plant_off _ _ _ _ (by
            simp [Keccak.length_bytesToBitsLE, nonceInput, rh']) _]
  have pkHash seed K (t : Fin s.params.k → Poly) :
      (G seed K).h256.readBytes (encodePublic s rho t) 64 =
        H.h256.readBytes (encodePublic s rho t) 64 := by
    apply plant_off
    rw [Keccak.length_bytesToBitsLE, encodePublic, List.length_append, rh, length_packCoeffs]
    cases s <;> decide
  change rowSigner (G seed K) s seed = rowSigner (G z z) s z
  have expansion (u v : FixedBytes 32) :
      (G u v).expandKeySeed s u = FixedBytes.toList (n := 128) (Fin.append p v) :=
    Xofs.expandKeySeed_withKeySeedExpansion H s u _
  simp only [rowSigner, Xofs.keyGen, expansion, (fields K).1, (fields K).2.1,
    (fields K).2.2, (fields z).1, (fields z).2.1, (fields z).2.2,
    Xofs.expandA_congr (H := H) (K := G seed K) rfl,
    Xofs.expandA_congr (H := H) (K := G z z) rfl, short, pkHash,
    Option.pure_def, Option.bind_eq_bind]
  cases eqA : H.expandA s rho
  · rfl
  rename_i A
  cases eqU : tabulate _ (fun i : Fin s.params.ℓ => H.secretPoly s rho' i.val)
  · rfl
  rename_i u
  cases eqV : tabulate _ (fun i : Fin s.params.k => H.secretPoly s rho' (s.params.ℓ + i.val))
  · rfl
  rename_i v
  simp only [Option.bind_some, Option.map_some, pkHash]
  let t := fun i => (Vector.ofFn (fun i => Vector.ofFn ((moduleSISMap A u + v) i))).get i |>.get
  let sk : PrivateKey s := ⟨rho, z.toList, H.h256.readBytes (encodePublic s rho t) 64,
    u, v, fun i j => ((power2Round 8380417 13 (t i j)).2 : ZMod 8380417)⟩
  let view (reply : Row → SigningQuery → Option (List Byte)) : Option RowSigner :=
    some ⟨encodePublic s rho t, H.h256.readBytes (encodePublic s rho t) 64, reply⟩
  apply congrArg view
  funext r q
  have run seed' K' := sign_plant H s seed' (Fin.append p K') sk rh
    (FixedBytes.length_toList z) (H.h256.length_read ..) K' q r
  exact (run seed K).trans (run z z).symm

namespace QuantumSigningForger

private noncomputable def serviceAddress (C : QuantumSigningForger) (device : Xofs) (s : Level)
    (service : Option RowSigner) {n : ℕ} (rows : SigningMaskSeeds n) (j : ℕ) :=
  C.addressLaw device s RowSigner.publicKey service (fun _ _ => 0)
    (List.ofFn fun i μ => rows (i, μ)) (fun sv r => C.signingCommand device (sv.reply r)) j

private noncomputable def observations (C : QuantumSigningForger) (device : Xofs) (s : Level)
    (service : Option RowSigner) {n : ℕ} (rows : SigningMaskSeeds n) (j : ℕ) :=
  (C.serviceAddress device s service rows j).map
    (signingSeedCandidates (C := C) (service.map RowSigner.hash))

private theorem fixedPrediction_eq (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) (a b : ℕ) {n : ℕ} (rows : SigningMaskSeeds n) (j : ℕ) :
    C.fixedPrediction s base seed a b rows j =
      (base.uniformPrefixes a b).bind fun H =>
        (C.observations H s (rowSigner H s seed) rows j).map fun guesses =>
          guesses.contains (Keccak.bytesToBitsLE (signingSeedBytes H s seed)) := by
  unfold fixedPrediction
  congr 1
  funext H
  unfold observations serviceAddress rowSigner rowAddress addressLaw publicHash
  cases H.keyGen s seed with
  | none => simp [withTrialSetup]
  | some k =>
    simp only [Option.map_some, withTrialSetup, PMF.map_comp, Function.comp_def]
    cases H.expandA s (k.publicKey.take 32) <;> rfl

/-- Predict the private signing seed in an experiment with an independently drawn expansion.
Both runs use the same generated public key, its hash, and the same independent mask-seed
rows for adaptive signing requests.
With `planted` the device sees the 128 expansion bytes at the FIPS key-generation address.
Otherwise all its coherent queries use the original background table. -/
noncomputable def keySeedDeviceGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b n j : ℕ) (planted : Bool) : Game := do
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let rows ← PMF.uniformOfFintype (SigningMaskSeeds n)
  let H ← base.uniformPrefixes a b
  let p ← PMF.uniformOfFintype (FixedBytes 96)
  let K ← PMF.uniformOfFintype (FixedBytes 32)
  let device := if planted then H.withKeySeedExpansion s seed (Fin.append p K) else H
  let service := rowSigner (setupOracle H s p) s fun _ => 0
  let guesses ← C.observations device s service rows j
  return guesses.contains (Keccak.bytesToBitsLE K.toList)

/-- Programming the expansion at the hidden input reproduces the original prediction
experiment exactly, including the encoded public key, signing replies and failed setup. -/
theorem keySeedDeviceGame_true (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 272 ≤ a) (hb : 128 ≤ b) (n j : ℕ) :
    C.keySeedDeviceGame s base a b n j true = C.signingSeedPredictionGame s base a b n j := by
  simp only [keySeedDeviceGame, signingSeedPredictionGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, ↓reduceIte, fixedPrediction_eq]
  congr 1
  funext seed
  congr 1
  funext rows
  let run (H : Xofs) :=
    (C.observations H s (rowSigner H s seed) rows j).map fun guesses =>
      guesses.contains (Keccak.bytesToBitsLE (signingSeedBytes H s seed))
  change _ = (base.uniformPrefixes a b).bind run
  apply Eq.trans _ (uniform_plant base s seed ha hb run)
  apply congrArg (fun f => (base.uniformPrefixes a b).bind f)
  funext H
  have split := PMF.uniformOfFintype_bind_bind_equiv (Fin.appendEquiv 96 32 (α := Byte))
    (fun out => run (H.withKeySeedExpansion s seed out))
  refine Eq.trans ?_ split
  apply congrArg (fun f => (PMF.uniformOfFintype (FixedBytes 96)).bind f)
  funext p
  apply congrArg (fun f => (PMF.uniformOfFintype (FixedBytes 32)).bind f)
  funext K
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk, run, rowSigner_plant, signingSeedBytes,
    Xofs.expandKeySeed_withKeySeedExpansion, FixedBytes.toList, List.ofFn_fin_append]
  rfl

private theorem two_guesses {C : QuantumSigningForger} (hash : Option (List Byte))
    (addr : Option (Address C)) :
    ((PMF.uniformOfFintype (FixedBytes 32)).map fun K =>
      (signingSeedCandidates (C := C) hash addr).contains (Keccak.bytesToBitsLE K.toList)) true ≤
        2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let bits (K : FixedBytes 32) := Keccak.bytesToBitsLE K.toList
  have inj : Function.Injective bits := fun x y h =>
    List.ofFn_inj.mp (Keccak.bytesToBitsLE_injective h)
  let matched (candidate : Option (List Bool)) (K : FixedBytes 32) :=
    decide (candidate = some (bits K))
  have one (candidate) :
      ((PMF.uniformOfFintype (FixedBytes 32)).map (matched candidate)) true ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    apply (PMF.uniformOfFintype_bind_pure_apply_true_le ?_).trans_eq
    · rw [card_hedge, Nat.cast_pow, Nat.cast_ofNat]
    · intro x hx y hy
      exact inj (Option.some.inj ((of_decide_eq_true hx).symm.trans (of_decide_eq_true hy)))
  let pub := hash.map fun tr => Keccak.bytesToBitsLE (tr.take 32)
  let qry := queryKeyPrefix (C := C) addr
  refine (PMF.map_true_le_add _ (A := matched pub) (B := matched qry) ?_).trans
    ((add_le_add (one pub) (one qry)).trans_eq (two_mul _).symm)
  intro K _ h
  rw [List.contains_iff_mem, signingSeedCandidates, List.mem_append] at h
  simpa only [Option.mem_toList, Option.mem_def, pub, qry, matched, bits,
    decide_eq_true_eq] using h

/-- With background coherent access, even an adaptive signed execution gives at most two
guesses for an independent uniform 32-byte private signing seed. -/
theorem keySeedDeviceGame_false_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b n j : ℕ) :
    (Game.succProbability (C.keySeedDeviceGame s base a b n j false) : ℝ) ≤ 2 / 2 ^ 256 := by
  let B := 2 * (2 ^ 256 : ℝ≥0∞)⁻¹
  have bound : C.keySeedDeviceGame s base a b n j false true ≤ B := by
    simp only [keySeedDeviceGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
    iterate 3
      apply PMF.bind_apply_le_on_support
      intro _ _
    simp only [observations, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    apply PMF.bind_apply_le_on_support
    intro addr _
    exact two_guesses _ addr
  have r := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr (by positivity))) bound
  simpa only [B, Game.coe_succProbability, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, div_eq_mul_inv] using r

private theorem before_first_query {C : QuantumSigningForger} {α : Type} (p : Program C α) :
    OracleComp.QueriesSatisfy (fun q => isXofQuery (C := C) q = false)
      (queryPrefix (C := C) p 0) := by
  induction p with
  | pure a => exact .pure _
  | liftBind q k ih =>
    cases h : isXofQuery (C := C) q with
    | true => simp only [queryPrefix, h, beq_self_eq_true, Bool.and_self, ↓reduceIte]; exact .pure _
    | false =>
      simp only [queryPrefix, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Bool.toNat_false, Nat.sub_zero]
      exact OracleComp.QueriesSatisfy.liftBind_iff.mpr ⟨h, ih⟩

private theorem first_serviceAddress (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (seed : FixedBytes 32) (out : FixedBytes 128) (sv : Option RowSigner) {n : ℕ}
    (rows : SigningMaskSeeds n) :
    C.serviceAddress (H.withKeySeedExpansion s seed out) s sv rows 0 =
      C.serviceAddress H s sv rows 0 := by
  simp only [serviceAddress, addressLaw, withTrialSetup,
    Xofs.expandA_congr (H := H) (K := H.withKeySeedExpansion s seed out) rfl]
  cases sv with
  | none => rfl
  | some sv =>
    dsimp only
    cases H.expandA s (sv.publicKey.take 32) with
    | none => rfl
    | some A =>
      apply congrArg (fun p : StateT (State C × List Row) PMF Bool =>
        ((p.run (C.initial, List.ofFn fun i μ => rows (i, μ))).map
          (fun (found, st, _) => (found, st))).bind (addressRead C))
      apply (before_first_query _).interpret_congr
      rintro (coin | cmd | sign) h
      · rfl
      · cases cmd with
        | query => exact Bool.noConfusion (show true = false from h)
        | service op _ => exact op.elim
        | gate _ | measure _ =>
          funext st
          obtain ⟨st, tape⟩ := st
          simp only [OracleComp.withSampleListWhen, isSigningCall, Sum.elim_inr, Sum.elim_inl,
            Bool.false_eq_true, ↓reduceIte, signingCommand, deviceCommand, OracleComp.sumHandler,
            deviceHandler_gate, deviceHandler_measure, DeviceState.instruction_apply,
            OracleGateCode.toPlacedGate?]
      · rfl

/-- Even with adaptive signing before the first coherent query, the original predictor
in the independent-row game has success at most `2 / 2^256` when the oracle covers key expansion. -/
theorem signingSeedPredictionGame_zero_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 272 ≤ a) (hb : 128 ≤ b) (n : ℕ) :
    (Game.succProbability (C.signingSeedPredictionGame s base a b n 0) : ℝ) ≤ 2 / 2 ^ 256 := by
  rw [← C.keySeedDeviceGame_true s base ha hb]
  have eq : C.keySeedDeviceGame s base a b n 0 true = C.keySeedDeviceGame s base a b n 0 false := by
    simp only [keySeedDeviceGame, Bool.false_eq_true, ↓reduceIte, observations,
      first_serviceAddress]
  rw [eq]
  exact C.keySeedDeviceGame_false_le s base a b n 0

private def queriesKeySeed {C : QuantumSigningForger} (s : Level) (seed : FixedBytes 32)
    (addr : Option (Address C)) : Bool :=
  match addr with
  | none => false
  | some v => v 0 && Xofs.unpad (List.ofFn (fun i : Fin (C.addressBits + 1) => v i.succ)) ==
      some (keySeedInput s seed)

private theorem queriesKeySeed_of_change {C : QuantumSigningForger} (s : Level) (H : Xofs)
    (seed : FixedBytes 32) (out : FixedBytes 128) (addr : Option (Address C))
    (hit : addr.any (fun v => decide ((H.withKeySeedExpansion s seed out).queryTable C.addressBits
      C.responseBytes v ≠ H.queryTable C.addressBits C.responseBytes v)) = true) :
    queriesKeySeed s seed addr := by
  cases addr with
  | none => exact Bool.noConfusion hit
  | some v =>
    simp only [Option.any_some, decide_eq_true_eq] at hit
    simp only [Xofs.queryTable] at hit
    cases e : Xofs.unpad (List.ofFn fun i : Fin (C.addressBits + 1) => v i.succ) with
    | none => exact (hit (by rw [e])).elim
    | some x =>
      rw [e] at hit
      cases tag : v 0 with
      | false => exact (hit (by rw [tag]; rfl)).elim
      | true =>
        by_cases h : x = keySeedInput s seed
        · simp only [queriesKeySeed, tag, e, h, beq_self_eq_true, Bool.and_self]
        · exact (hit (by simp only [tag, ↓reduceIte, Xofs.withKeySeedExpansion,
            ExtendableOutput.withPrefixes, ite_eq_right h])).elim

private theorem changed_keySeed_le (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (out : FixedBytes 128) (addr : Option (Address C)) :
    ((PMF.uniformOfFintype (FixedBytes 32)).bind fun seed => PMF.pure
      (addr.any fun v => decide ((H.withKeySeedExpansion s seed out).queryTable
        C.addressBits C.responseBytes v ≠ H.queryTable C.addressBits C.responseBytes v))) true ≤
        (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply (PMF.uniformOfFintype_bind_pure_apply_true_le ?_).trans_eq
  · rw [card_hedge, Nat.cast_pow, Nat.cast_ofNat]
  · intro x hx y hy
    have hx := queriesKeySeed_of_change (C := C) s _ x _ addr hx
    have hy := queriesKeySeed_of_change (C := C) s _ y _ addr hy
    cases addr with
    | none => exact Bool.noConfusion (show false = true from hx)
    | some v =>
      simp only [queriesKeySeed, Bool.and_eq_true, beq_iff_eq] at hx hy
      have eq := Option.some.inj (hx.2.symm.trans hy.2)
      exact List.ofFn_inj.mp (List.append_cancel_right (Keccak.bytesToBitsLE_injective eq))

/-- Measure the selected coherent address of the background device. Test whether the XOR
response at that address would change if the 128-byte key expansion were installed. -/
noncomputable def keySeedQueryHit (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b n j : ℕ) : Game := do
  let rows ← PMF.uniformOfFintype (SigningMaskSeeds n)
  let H ← base.uniformPrefixes a b
  let p ← PMF.uniformOfFintype (FixedBytes 96)
  let addr ← C.serviceAddress H s (rowSigner (setupOracle H s p) s fun _ => 0) rows j
  let K ← PMF.uniformOfFintype (FixedBytes 32)
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  return addr.any fun v => decide ((H.withKeySeedExpansion s seed (Fin.append p K)).queryTable
    C.addressBits C.responseBytes v ≠ H.queryTable C.addressBits C.responseBytes v)

/-- At each query of the background device, the probability of detecting the programmed
key-generation response is at most `2⁻²⁵⁶`, including after adaptive signing and measurements. -/
theorem keySeedQueryHit_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b n j : ℕ) :
    (Game.succProbability (C.keySeedQueryHit s base a b n j) : ℝ) ≤ 1 / 2 ^ 256 := by
  have bound : C.keySeedQueryHit s base a b n j true ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    simp only [keySeedQueryHit, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    refine PMF.bind_apply_le_on_support _ fun _ _ => ?_
    refine PMF.bind_apply_le_on_support _ fun H _ => ?_
    refine PMF.bind_apply_le_on_support _ fun p _ => ?_
    refine PMF.bind_apply_le_on_support _ fun addr _ => ?_
    exact PMF.bind_apply_le_on_support _ fun K _ => changed_keySeed_le C s H (Fin.append p K) addr
  simpa only [Game.coe_succProbability, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, one_div] using ENNReal.toReal_mono (by simp) bound

/-- For any retained reference state independent of the hidden 32-byte key-generation seed,
the mean squared displacement of the actual XOR gate when the 128 expansion bytes are
installed is at most `4 / 2^256`. The state and expansion may depend on the entire
background table. The device can request any number of response bytes. -/
theorem mean_keySeedQueryDisturbance_le (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (out : FixedBytes 128) {κ σ : Type} [Fintype κ] [DecidableEq κ]
    (st : DeviceState (C.addressBits + 2 + 8 * C.responseBytes + C.workQubits) κ σ) :
    let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
    ∑ seed : FixedBytes 32, ((PMF.uniformOfFintype (FixedBytes 32)) seed).toReal *
      xorQueryDisturbance
        ((H.withKeySeedExpansion s seed out).queryTable C.addressBits C.responseBytes)
        (H.queryTable C.addressBits C.responseBytes) A st.density ≤ 4 / 2 ^ 256 := by
  classical
  intro A
  let seeds := PMF.uniformOfFintype (FixedBytes 32)
  let basis := POVM.basis.measureDensity st.density st.isDensityMatrix
  let changed := fun (seed : FixedBytes 32) (z : (Fin (Width C) → Bool) × κ) =>
    let x := (queryRegisters A z.1).1
    decide ((H.withKeySeedExpansion s seed out).queryTable C.addressBits C.responseBytes x ≠
      H.queryTable C.addressBits C.responseBytes x)
  have hit : (seeds.bind fun seed => basis.map (changed seed)) true ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    rw [PMF.bind_comm]
    apply PMF.bind_apply_le_on_support
    intro z _
    exact changed_keySeed_le C s H out (some (queryRegisters A z.1).1)
  have mean := ENNReal.toReal_mono (by simp) hit
  rw [Cslib.Probability.PMF.bind_apply_toReal] at mean
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at mean
  calc
    _ ≤ ∑ seed, (seeds seed).toReal * (4 * ((basis.map (changed seed)) true).toReal) := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (xorQueryDisturbance_le _ _ A st.isDensityMatrix)
        ENNReal.toReal_nonneg
    _ = 4 * ∑ seed, (seeds seed).toReal * ((basis.map (changed seed)) true).toReal := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_left_comm ..
    _ ≤ _ := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left mean (by norm_num : 0 ≤ (4 : ℝ))

open scoped ComplexOrder in
/-- Apply any binary measurement after the native query, allowing the measurement to depend on
the hidden seed. For a seed-independent input state, the mean square change in the square root
of the acceptance probability is at most `4 / 2^256`. -/
theorem mean_sq_sqrt_keySeedQuery_readout_le (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (out : FixedBytes 128) {κ σ : Type} [Fintype κ] [DecidableEq κ]
    (st : DeviceState (C.addressBits + 2 + 8 * C.responseBytes + C.workQubits) κ σ)
    (M : FixedBytes 32 → POVM Bool
      ((Fin (C.addressBits + 2 + 8 * C.responseBytes + C.workQubits) → Bool) × κ)) :
    let p := fun seed (G : Xofs) => (M seed).densityProb
      (st.instruction (G.queryTable C.addressBits C.responseBytes) .query).density true
    ∑ seed : FixedBytes 32, ((PMF.uniformOfFintype (FixedBytes 32)) seed).toReal *
      (√(p seed (H.withKeySeedExpansion s seed out)) - √(p seed H)) ^ 2 ≤ 4 / 2 ^ 256 := by
  classical
  intro p
  let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
  let U := fun (G : Xofs) => (onFirst (κ := κ)
    (xorQuery (G.queryTable C.addressBits C.responseBytes) A).matrix).val
  have born (seed) (G : Xofs) :
      p seed G = (M seed).densityProb (densityConj (U G) st.density) true := by
    simp only [p, DeviceState.instruction_apply, OracleGateCode.toPlacedGate?,
      Nat.le_add_right, ↓reduceDIte, DeviceState.evolve_density, U, coe_onFirst, A]
  refine le_trans (Finset.sum_le_sum fun seed _ => mul_le_mul_of_nonneg_left ?_
    ENNReal.toReal_nonneg) (C.mean_keySeedQueryDisturbance_le s H out st)
  let G := H.withKeySeedExpansion s seed out
  let D := U G - U H
  have diff := (M seed).abs_sqrt_densityProb_sub_le true st.isDensityMatrix.posSemidef (U G) (U H)
  rw [← born, ← born] at diff
  have pos := (st.isDensityMatrix.posSemidef.mul_mul_conjTranspose_same D).trace_nonneg
  change _ ≤ (densityConj D st.density).trace.re
  rw [← sq_abs, ← Real.sq_sqrt (show 0 ≤ (densityConj D st.density).trace.re by
    simpa only [densityConj_apply] using (Complex.nonneg_iff.mp pos).1)]
  exact pow_le_pow_left₀ (abs_nonneg _) diff 2

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
