/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import CslibFrontier.Probability.PMF.UniformExtend
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.PMF.Bind

/-!
# The public-key hash in seeded ML-DSA

In [FIPS 204][NISTFIPS204], Algorithm 6, the SHAKE256 calls that determine the public key
have 34-byte and 66-byte inputs. The final hash reads the encoded public key itself. Its length
is different from both earlier input lengths at every FIPS level. We use this distinction on
the actual finite random table, retaining the dependence of the encoded key on the short reads.
The independence law and its public-key-prefix bound are original deductions for this game.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability ExtendableOutput
open scoped ENNReal

private abbrev keyBits (s : Level) := 8 * (32 + 320 * s.params.k)

private abbrev KeyCell (s : Level) (a b : ℕ) :=
  {p : RawWord a × Fin b // p.1.1.val = keyBits s}

private noncomputable def replaceRows {s : Level} {a b : ℕ}
    (t : Table a b) (g : KeyCell s a b → Byte) : Table a b :=
  Function.extend Subtype.val g t

private theorem short_read {s : Level} {a b : ℕ} (t : Table a b) (g : KeyCell s a b → Byte)
    (base : ExtendableOutput) (x : List Bool) (hx : x.length ≤ 528) (n : ℕ) :
    (install base (replaceRows t g)).read x n = (install base t).read x n := by
  refine List.ext_getElem (by simp only [length_read]) fun i hi _ => ?_
  have hin : i < n := by simpa only [length_read] using hi
  rw [getElem_read _ _ hin, getElem_read _ _ hin]
  simp only [byteAt_install]
  split
  · apply Function.extend_apply'
    rintro ⟨p, hp⟩
    have len := p.2
    rw [hp] at len
    change x.length = keyBits s at len
    have : 528 < keyBits s := by cases s <;> decide
    lia
  · rfl

private abbrev pub (H : Xofs) (s : Level) (seed : FixedBytes 32) :=
  (H.keyGen s seed).map KeyPair.publicKey

private theorem pub_replaceRows {s : Level} {a b : ℕ} (H : Xofs) (t : Table a b)
    (g : KeyCell s a b → Byte) (seed : FixedBytes 32) :
    pub ⟨H.h128, install H.h256 (replaceRows t g)⟩ s seed =
      pub ⟨H.h128, install H.h256 t⟩ s seed := by
  let R : Xofs := ⟨H.h128, install H.h256 (replaceRows t g)⟩
  let G : Xofs := ⟨H.h128, install H.h256 t⟩
  change pub R s seed = pub G s seed
  have exp : R.expandKeySeed s seed = G.expandKeySeed s seed := by
    apply short_read
    rw [length_keySeedInput]; decide
  let rho := ((G.expandKeySeed s seed).drop 32).take 64
  have secret (i : ℕ) : R.secretPoly s rho i = G.secretPoly s rho i := by
    have eq := short_read t g H.h256 (Keccak.bytesToBitsLE (nonceInput rho i)) (by
      have := List.length_take_le 64 ((G.expandKeySeed s seed).drop 32)
      simp only [nonceInput, Keccak.length_bytesToBitsLE, List.length_append, List.length_cons,
        List.length_nil]
      dsimp only [rho]
      lia) 481
    simp only [Xofs.secretPoly, R, G, ExtendableOutput.readBytes, eq]
  have expandS : R.expandS s rho = G.expandS s rho := by
    simp only [Xofs.expandS, secret]
  have mat (r : List Byte) : R.expandA s r = G.expandA s r := rfl
  unfold pub Xofs.keyGen
  rw [exp]
  dsimp only
  rw [show ((G.expandKeySeed s seed).drop 32).take 64 = rho from rfl, expandS, mat]
  cases G.expandA s ((G.expandKeySeed s seed).take 32) with
  | none => simp only [Option.bind_eq_bind, Option.bind_none, Option.map_none]
  | some _ =>
    rcases G.expandS s rho with _ | ⟨_, _⟩
    · simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map_none]
    · simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some]

private theorem pub_length {H : Xofs} {s : Level} {seed : FixedBytes 32} {pk : List Byte}
    (h : pub H s seed = some pk) : pk.length = 32 + 320 * s.params.k := by
  obtain ⟨keys, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rho, sk, _, eq, _⟩ := privateKey_of_keyGen hk
  rw [eq, encodePublic, List.length_append, FixedBytes.length_toList, length_packCoeffs]

private def rowPos {s : Level} {a b : ℕ} {x : List Bool} (hx : x.length = keyBits s)
    (ha : keyBits s ≤ a) (hb : 64 ≤ b) : Fin 64 ↪ KeyCell s a b where
  toFun i := ⟨(word x (hx.le.trans ha), Fin.castLE hb i), hx⟩
  inj' _ _ eq := Fin.ext (congrArg (fun p => p.val.2.val) eq)

private theorem read_at_key {s : Level} {a b : ℕ} (t : Table a b) (g : KeyCell s a b → Byte)
    (base : ExtendableOutput) {x : List Bool} (hx : x.length = keyBits s)
    (ha : keyBits s ≤ a) (hb : 64 ≤ b) :
    (install base (replaceRows t g)).read x 64 = FixedBytes.toList (g ∘ rowPos hx ha hb) := by
  refine List.ext_getElem (by simp only [length_read, FixedBytes.length_toList]) fun i hi _ => ?_
  have hin : i < 64 := by simpa only [length_read] using hi
  rw [getElem_read _ _ hin, byteAt_install, dite_eq_left ⟨hx.le.trans ha, hin.trans_le hb⟩]
  change Function.extend Subtype.val g t ((rowPos hx ha hb ⟨i, hin⟩).val) = _
  rw [Subtype.val_injective.extend_apply]
  simp only [FixedBytes.toList, List.getElem_ofFn, Function.comp_apply]

private theorem table_publicKeyHash (H : Xofs) (s : Level) (seed : FixedBytes 32)
    {a b : ℕ} (ha : keyBits s ≤ a) (hb : 64 ≤ b) :
    let stream (t : Table a b) : Xofs := ⟨H.h128, install H.h256 t⟩
    ((PMF.uniformOfFintype (Table a b)).map fun t =>
      (pub (stream t) s seed).map fun pk => (pk, (stream t).h256.readBytes pk 64)) =
    (PMF.uniformOfFintype (Table a b)).bind fun t =>
      (PMF.uniformOfFintype (FixedBytes 64)).map fun v =>
        (pub (stream t) s seed).map (fun pk => (pk, v.toList)) := by
  classical
  intro stream
  let U := PMF.uniformOfFintype (Table a b)
  let observe (t : Table a b) := PMF.pure ((pub (stream t) s seed).map fun pk =>
    (pk, (stream t).h256.readBytes pk 64))
  change U.bind observe = _
  rw [← PMF.uniformOfFintype_bind_bind_extend (Subtype.val : KeyCell s a b → _) observe]
  apply congrArg (fun f => U.bind f)
  funext t
  have unchanged (g : KeyCell s a b → Byte) :
      pub (stream (replaceRows t g)) s seed = pub (stream t) s seed :=
    pub_replaceRows H t g seed
  change ((PMF.uniformOfFintype (KeyCell s a b → Byte)).map fun g =>
    (pub (stream (replaceRows t g)) s seed).map fun pk =>
      (pk, (stream (replaceRows t g)).h256.readBytes pk 64)) = _
  simp only [unchanged]
  cases hp : pub (stream t) s seed with
  | none => simp only [Option.map_none, PMF.map, Function.comp_def, PMF.bind_const]
  | some pk =>
    have hx : (Keccak.bytesToBitsLE pk).length = keyBits s := by
      rw [Keccak.length_bytesToBitsLE, pub_length hp]
    have uniform := PMF.uniformOfFintype_pi_map_comp_embedding (α := Byte) (rowPos hx ha hb)
    have eq := congrArg (PMF.map (fun v : FixedBytes 64 => some (pk, v.toList))) uniform
    rw [PMF.map_comp] at eq
    have raw (g : KeyCell s a b → Byte) :
        (install H.h256 (replaceRows t g)).read (Keccak.bytesToBitsLE pk) 64 =
          FixedBytes.toList (g ∘ rowPos hx ha hb) := read_at_key t g H.h256 hx ha hb
    simpa only [stream, ExtendableOutput.readBytes, Option.map_some, Function.comp_def, raw]
      using eq

/-- In the finite ideal-XOF experiment, the public key obtained from Algorithm 6 and its
64-byte hash have exactly the law of the same optional public key paired on success with
an independent uniform 64-byte string. This holds for every fixed 32-byte key-generation seed
and retains the probability of Appendix C setup failure. -/
theorem uniformPrefixes_publicKeyHash (base : Xofs) (s : Level) (seed : FixedBytes 32)
    {a b : ℕ} (ha : 8 * (32 + 320 * s.params.k) ≤ a) (hb : 64 ≤ b) :
    ((base.uniformPrefixes a b).map fun H => (H.keyGen s seed).map fun keys =>
      (keys.publicKey, H.h256.readBytes keys.publicKey 64)) =
    (base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 64)).map fun v =>
        (H.keyGen s seed).map (fun keys => (keys.publicKey, v.toList)) := by
  let U := PMF.uniformOfFintype (Table a b)
  have tables : base.uniformPrefixes a b = U.bind fun t₁ =>
      U.map fun t₂ => ⟨install base.h128 t₁, install base.h256 t₂⟩ := by
    rw [independent_tables]
    exact PMF.bind_comm U U _
  rw [tables]
  simp only [PMF.map_bind, PMF.bind_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  congr 1
  funext t
  simpa only [pub, Option.map_map, Function.comp_def] using
    table_publicKeyHash ({base with h128 := install base.h128 t}) s seed ha hb

private theorem uniform_hash_hit (pk : List Byte) :
    ((PMF.uniformOfFintype (FixedBytes 64)).map fun v => decide (v.toList = pk.take 64)) true ≤
      (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  change ((PMF.uniformOfFintype (FixedBytes 64)).bind fun v =>
    PMF.pure (decide (v.toList = pk.take 64))) true ≤ _
  rw [PMF.bind_pure_decide_apply_true]
  have bound := PMF.toOuterMeasure_uniformOfFintype_le_of_subsingleton
    (s := {v : FixedBytes 64 | v.toList = pk.take 64})
    (fun a ha b hb => List.ofFn_inj.mp (ha.trans hb.symm))
  have card : Fintype.card (FixedBytes 64) = 2 ^ 512 := by
    change Fintype.card (Fin 64 → Fin 256) = 2 ^ 512
    rw [show (512 : ℕ) = 8 * 64 by decide, pow_mul, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin]
    rfl
  simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- Under the actual seeded key-generation law on the finite ideal streams, the probability
of successful setup with the first 64 public-key bytes equal to its SHAKE256 hash is at most
`2⁻⁵¹²`. The random table widths are fixed before drawing the key-generation seed. -/
theorem uniformPrefixes_publicKeyPrefix_le (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 8 * (32 + 320 * s.params.k) ≤ a) (hb : 64 ≤ b) :
    ((base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
      PMF.pure (decide (H.h256.readBytes keys.publicKey 64 = keys.publicKey.take 64))) true ≤
      (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  unfold Xofs.keyExperiment
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_on_support
  intro seed _
  let test (result : Option (List Byte × List Byte)) :=
    result.any fun p => decide (p.2 = p.1.take 64)
  have eq := congrArg (PMF.map test) (uniformPrefixes_publicKeyHash base s seed ha hb)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at eq
  have realize (H : Xofs) :
      PMF.pure (test ((H.keyGen s seed).map fun k =>
        (k.publicKey, H.h256.readBytes k.publicKey 64))) =
      (match H.keyGen s seed with
       | none => PMF.pure false
       | some k => PMF.pure (decide (H.h256.readBytes k.publicKey 64 = k.publicKey.take 64))) := by
    cases H.keyGen s seed <;> rfl
  have game := congrArg (base.uniformPrefixes a b).bind (funext realize)
  apply le_of_eq_of_le (congrArg (fun d : Game => d true) game.symm)
  change ((base.uniformPrefixes a b).map fun H => test ((H.keyGen s seed).map fun k =>
    (k.publicKey, H.h256.readBytes k.publicKey 64))) true ≤ _
  rw [eq]
  apply PMF.bind_apply_le_on_support
  intro H _
  cases H.keyGen s seed with
  | none => simp [test, PMF.map, Function.comp_def]
  | some k => exact uniform_hash_hit k.publicKey

end Cslib.Crypto.MLDSA.FIPS204
