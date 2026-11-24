/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FullPairMLWE
-- Reads private `PostKey`, `observePair`, `separate_secret`, and `Xofs.withExpandSStream`.
import all CslibFrontier.Crypto.Computational.MLDSA.FullPairMLWE
import CslibFrontier.Probability.PMF.UniformExtend

/-!
# Coupling private and shared ML-DSA key expansion

[FIPS 204][NISTFIPS204], Algorithm 6, derives both a 32-byte public matrix seed and a 64-byte
secret expansion seed from one SHAKE256 read. Algorithm 33 reads the rows of both short vectors
at that second seed with successive two-byte counters. The same inputs are available to the
forger through its quantum XOF interface.

`QuantumSigningForger.secretExpansionViews_games` expresses both online games as continuations of
one random setup. Resampling the secret rows preserves the whole oracle distribution because
their 528-bit addresses differ from the 272-bit input that determines those addresses.
`SecretExpansionViews.agree_of_mem` locates every byte at which the two online oracles can differ.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204
open Cslib.Probability ExtendableOutput

private def matrixSeed (H : Xofs) (s : Level) (seed : FixedBytes 32) : FixedBytes 32 :=
  fun i => ((H.expandKeySeed s seed).take 32)[i.val]!

private theorem matrixSeed_bytes (H : Xofs) (s : Level) (seed : FixedBytes 32) :
    (matrixSeed H s seed).toList = (H.expandKeySeed s seed).take 32 := by
  have len : (H.expandKeySeed s seed).length = 128 := H.h256.length_read ..
  let rho := (H.expandKeySeed s seed).take 32
  have hr : rho.length = 32 := by simp [rho, len]
  obtain ⟨r, eq⟩ := FixedBytes.exists_toList hr
  change FixedBytes.toList (n := 32) (fun i => rho[i.val]!) = rho
  rw [← eq]
  congr 1
  funext i
  simp only [FixedBytes.toList, List.length_ofFn, getElem!_pos, i.isLt, List.getElem_ofFn]

private def expansionSeed (H : Xofs) (s : Level) (seed : FixedBytes 32) : FixedBytes 64 :=
  fun j => ((H.expandKeySeed s seed).drop 32)[j.val]!

private theorem expansionSeed_bytes (H : Xofs) (s : Level) (seed : FixedBytes 32) :
    (expansionSeed H s seed).toList = ((H.expandKeySeed s seed).drop 32).take 64 := by
  have len : (H.expandKeySeed s seed).length = 128 := H.h256.length_read ..
  apply List.ext_getElem
  · simp [len]
  · intro i hi _
    have small : i < 64 := by simpa using hi
    have hd : i < ((H.expandKeySeed s seed).drop 32).length := by simp [len]; lia
    simp only [FixedBytes.toList, List.getElem_ofFn, expansionSeed, List.getElem_take,
      getElem!_pos ((H.expandKeySeed s seed).drop 32) i hd]

private def atTable {a b : ℕ} (base : Xofs) (T : Table a b) : Xofs :=
  {base with h256 := install base.h256 T}

private def slots {a b : ℕ} (s : Level) (base : Xofs) (seed : FixedBytes 32)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (T : Table a b) :=
  secretPoint s (expansionSeed (atTable base T) s seed) ha hb

private theorem read_off_slots {a b : ℕ} (s : Level) (base : Xofs) (seed : FixedBytes 32)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (T : Table a b) (fresh : Nonce s × Fin 481 → Byte)
    (x : List Bool) (away : ∀ j, x ≠ nonceWord s (expansionSeed (atTable base T) s seed) j)
    (n : ℕ) :
    (atTable base (Function.extend (slots s base seed ha hb T) fresh T)).h256.read x n =
      (atTable base T).h256.read x n := by
  apply read_eq_of_byteAt_eq
  intro i hi
  simp only [atTable, byteAt_install]
  split
  next h =>
    apply Function.extend_apply'
    rintro ⟨j, eq⟩
    exact away j.1 (word_inj (hx := (length_nonceInput_bits _ _).le.trans ha) (hy := h.1)
      (congrArg Prod.fst eq)).symm
  next => rfl

private theorem fixed_expansion {a b : ℕ} (s : Level) (base : Xofs) (seed : FixedBytes 32)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (T : Table a b) (v : Nonce s × Fin 481 → Byte) :
    (atTable base (Function.extend (slots s base seed ha hb T) v T)).expandKeySeed s seed =
      (atTable base T).expandKeySeed s seed := by
  apply read_off_slots
  intro j h
  have len := congrArg List.length h
  rw [length_keySeedInput] at len
  change 272 = (Keccak.bytesToBitsLE (nonceInput _ _)).length at len
  rw [length_nonceInput_bits] at len
  contradiction

private theorem uniform_secret_resample {a b : ℕ} (s : Level) (base : Xofs)
    (seed : FixedBytes 32) (ha : 528 ≤ a) (hb : 481 ≤ b) {α : Type} (run : Xofs → PMF α) :
    ((PMF.uniformOfFintype (Table a b)).bind fun T =>
      (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).bind fun v =>
        run (atTable base (Function.extend (slots s base seed ha hb T) v T))) =
      (PMF.uniformOfFintype (Table a b)).bind fun T => run (atTable base T) := by
  apply PMF.uniformOfFintype_bind_bind_adaptiveExtend (slots s base seed ha hb) _
    (fun T => run (atTable base T))
  intro T v
  apply congrArg (fun r => secretPoint s r ha hb)
  funext i
  exact congrArg (fun l : List Byte => (l.drop 32)[i.val]!) (fixed_expansion s base seed ha hb T v)

private noncomputable def atSeed {s : Level} (H : Xofs) (seed : FixedBytes 32)
    (run : PostKey s) : Game :=
  let ex := H.expandKeySeed s seed
  let rho := ex.take 32
  observePair (H.expandA s rho) (H.expandS s ((ex.drop 32).take 64))
    (run H (fun j => rho[j.val]!))

/-- The coupled FIPS setup before the signing adversary runs. Both games receive the
same public seed and pair. The distinguishing experiment determines which oracle they read. -/
structure SecretExpansionViews (s : Level) where
  /-- Raw XOFs with the sampled secret rows installed. -/
  shared : Xofs
  /-- Original raw XOFs, before installing those rows. -/
  background : Xofs
  /-- Original 32-byte key-generation seed, retained by the challenger. -/
  keySeed : FixedBytes 32
  /-- Secret 64-byte prefix derived at the actual key-generation input. -/
  secretSeed : FixedBytes 64
  /-- Matrix seed passed to the signer and encoded in the public key. -/
  publicSeed : FixedBytes 32
  /-- Matrix and full vector, absent on either native expansion failure. -/
  pair : Option (MLDSA.PublicKey s.params)

private def generatedPair {s : Level} (matrix : Option (PublicMatrix s))
    (short : Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly))) :
    Option (MLDSA.PublicKey s.params) := do
  let A ← matrix
  let (x, e) ← short
  return ⟨A, ModuleLWE.sample A x e⟩

private theorem observe_generatedPair {s : Level} (matrix : Option (PublicMatrix s))
    (short : Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly)))
    (run : MLDSA.PublicKey s.params → Game) :
    ((generatedPair matrix short).map run).getD (PMF.pure false) =
      observePair matrix short run := by
  cases matrix <;> cases short <;> rfl

private noncomputable def viewsAt {a b : ℕ} (s : Level) (base : Xofs) (seed : FixedBytes 32)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (T : Table a b) (rows : Nonce s × Fin 481 → Byte) :
    SecretExpansionViews s :=
  let H := atTable base T
  let rho := (H.expandKeySeed s seed).take 32
  { shared := atTable base (Function.extend (slots s base seed ha hb T) rows T)
    background := H
    keySeed := seed
    secretSeed := expansionSeed H s seed
    publicSeed := matrixSeed H s seed
    pair := generatedPair (H.expandA s rho) (vectors s (rowPair s rows)) }

/-- Joint distribution of the two online XOFs, derived seeds and the actual (possibly failed)
key-generation pair. The experiment resamples only the first 481 bytes in each of the secret
and error rows selected by Algorithm 6. -/
noncomputable def Xofs.sampleSecretExpansionViews (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) : PMF (SecretExpansionViews s) :=
  let U := PMF.uniformOfFintype (Table a b)
  U.bind fun T => U.bind fun M =>
    (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
      (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).map fun rows =>
        viewsAt s {base with h128 := install base.h128 M} seed ha hb T rows

private noncomputable def observeViews {s : Level} (share : Bool) (run : PostKey s)
    (v : SecretExpansionViews s) : Game :=
  (v.pair.map (run (if share then v.shared else v.background) v.publicSeed)).getD (PMF.pure false)

private theorem patched_trial {a b : ℕ} (s : Level) (base : Xofs) (seed : FixedBytes 32)
    (ha : 528 ≤ a) (hb : 481 ≤ b) (T : Table a b) (rows : Nonce s × Fin 481 → Byte)
    (run : PostKey s) :
    atSeed (atTable base (Function.extend (slots s base seed ha hb T) rows T)) seed run =
      observeViews true run (viewsAt s base seed ha hb T rows) := by
  let H := atTable base T
  let e := slots s base seed ha hb T
  let J := atTable base (Function.extend e rows T)
  let r := expansionSeed H s seed
  have val : J.expandS s r.toList = vectors s (rowPair s rows) := by
    have read := expandS_install s r ha hb base (Function.extend e rows T)
    have get (p : Nonce s × Fin 481) :
        Function.extend e rows T (secretPoint s r ha hb p) = rows p :=
      e.injective.extend_apply rows T p
    change (atTable base (Function.extend e rows T)).expandS s r.toList = _
    unfold atTable
    simpa only [get] using read
  unfold atSeed observeViews viewsAt
  dsimp only
  rw [fixed_expansion]
  change observePair _ (J.expandS s (((H.expandKeySeed s seed).drop 32).take 64)) _ = _
  rw [← expansionSeed_bytes, val]
  exact (observe_generatedPair ..).symm

private theorem shared_law {s : Level} (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) (run : PostKey s) :
    ((base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s (run H)) =
      (base.sampleSecretExpansionViews s ha hb).bind (observeViews true run) := by
  let U := PMF.uniformOfFintype (Table a b)
  let S := PMF.uniformOfFintype (FixedBytes 32)
  have atH (H : Xofs) : H.fullPairExperiment s (run H) = S.bind fun seed => atSeed H seed run :=
    Xofs.fullPairExperiment_eq_expand ..
  simp_rw [atH]
  rw [independent_tables]
  simp only [Xofs.sampleSecretExpansionViews, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  let F (M T : Table a b) := atTable {base with h128 := install base.h128 M} T
  change (U.bind fun T => U.bind fun M => S.bind fun seed => atSeed (F M T) seed run) =
    U.bind fun T => U.bind fun M => S.bind fun seed =>
      (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).bind fun v =>
        observeViews true run (viewsAt s {base with h128 := install base.h128 M} seed ha hb T v)
  conv_lhs => rw [PMF.bind_comm U U]
  conv_rhs => rw [PMF.bind_comm U U]
  apply congrArg (PMF.bind U ·)
  funext M
  conv_lhs => rw [PMF.bind_comm U S]
  conv_rhs => rw [PMF.bind_comm U S]
  apply congrArg (PMF.bind S ·)
  funext seed
  let B : Xofs := {base with h128 := install base.h128 M}
  change (U.bind fun T => atSeed (atTable B T) seed run) = _
  exact (uniform_secret_resample s B seed ha hb (fun H => atSeed H seed run)).symm.trans (by
    simp only [patched_trial, U, B])

private theorem detached_at_seed {s : Level} (base : Xofs) {a b : ℕ} (ha : 528 ≤ a)
    (hb : 481 ≤ b) (H : Xofs) (seed : FixedBytes 32) (run : PostKey s) :
    let ex := H.expandKeySeed s seed
    let A := H.expandA s (ex.take 32)
    let finish := run H (fun j => (ex.take 32)[j.val]!)
    ((base.uniformPrefixes a b).bind fun G =>
      observePair A (G.expandS s ((ex.drop 32).take 64)) finish) =
      (PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)).bind fun rows =>
        observePair A (vectors s (rowPair s rows)) finish := by
  intro ex A finish
  let r := expansionSeed H s seed
  have row := uniformPrefixes_secretRows base s r ha hb
  have uniform := PMF.uniformOfFintype_bind_map
    (fun x y => vectors s (x, y))
  rw [uniform, ← PMF.uniformOfFintype_map_equiv (rowPair s), PMF.map_comp] at row
  have eq := congrArg (PMF.bind · (fun v => observePair A v finish)) row
  simpa only [PMF.bind_map, Function.comp_def, r, expansionSeed_bytes] using eq

private theorem detached_law (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 481 ≤ b) :
    C.independentExpandSGame s base a b =
      (base.sampleSecretExpansionViews s ha hb).bind (observeViews false
        (fun H rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))) := by
  let run : PostKey s := fun H rho pk =>
    (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin)
  let R := base.uniformPrefixes a b
  let S := PMF.uniformOfFintype (FixedBytes 32)
  let V := PMF.uniformOfFintype (Nonce s × Fin 481 → Byte)
  have atH (H : Xofs) :
      (R.bind fun G => (H.withExpandSStream G).fullPairExperiment s (run H)) =
        S.bind fun seed => V.bind fun rows =>
          let rho := (H.expandKeySeed s seed).take 32
          observePair (H.expandA s rho) (vectors s (rowPair s rows))
            (run H (fun j => rho[j.val]!)) := by
    simp_rw [Xofs.fullPairExperiment_eq_expand, seed_keep]
    rw [PMF.bind_comm]
    apply congrArg (PMF.bind S ·)
    funext seed
    let rs := ((H.expandKeySeed s seed).drop 32).take 64
    have hr : rs.length = 64 := by
      have len : (H.expandKeySeed s seed).length = 128 := H.h256.length_read ..
      simp [rs, len]
    change (R.bind fun G => observePair _ ((H.withExpandSStream G).expandS s rs) _) = _
    simp_rw [separate_secret H _ s rs hr]
    exact detached_at_seed base ha hb H seed run
  change (R.bind fun H => R.bind fun G => (H.withExpandSStream G).fullPairExperiment s (run H)) = _
  simp_rw [atH]
  simp only [R, independent_tables, Xofs.sampleSecretExpansionViews, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, observeViews, viewsAt, observe_generatedPair]
  rfl

/-- The native public-pair signing game and the independent private-expansion game share
one setup distribution. They use its identical pair and published key. Only the XOFs passed
to adaptive signing, quantum queries and the final byte verifier differ. -/
theorem QuantumSigningForger.secretExpansionViews_games (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) :
    let run := fun H rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin)
    let V := base.sampleSecretExpansionViews s ha hb
    (((base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s (run H)) =
      V.bind fun v => (v.pair.map (run v.shared v.publicSeed)).getD (PMF.pure false)) ∧
    (C.independentExpandSGame s base a b =
      V.bind fun v => (v.pair.map (run v.background v.publicSeed)).getD (PMF.pure false)) :=
  ⟨shared_law base ha hb _, detached_law C s base ha hb⟩

/-- The coupled views expand the same original 32-byte key seed to the same 128 bytes.
Their published seed and private row prefix are the first 32 and following 64 of these bytes. -/
theorem SecretExpansionViews.seeds_of_mem {base : Xofs} {s : Level} {a b : ℕ}
    {ha : 528 ≤ a} {hb : 481 ≤ b} {v : SecretExpansionViews s}
    (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support) :
    let ex := v.background.expandKeySeed s v.keySeed
    v.shared.expandKeySeed s v.keySeed = ex ∧ v.publicSeed.toList = ex.take 32 ∧
      v.secretSeed.toList = (ex.drop 32).take 64 := by
  obtain ⟨T, _, M, _, seed, _, rows, _, rfl⟩ := (by
    simpa only [Xofs.sampleSecretExpansionViews, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] using hv)
  let B : Xofs := {base with h128 := install base.h128 M}
  let H := atTable B T
  exact ⟨fixed_expansion s B seed ha hb T rows, matrixSeed_bytes H s seed,
    expansionSeed_bytes H s seed⟩

/-- The coupled views have identical SHAKE128 streams and identical SHAKE256 bytes except at
the first 481 positions of an Algorithm 33 row. The nonce range includes both vectors. -/
theorem SecretExpansionViews.agree_of_mem {base : Xofs} {s : Level} {a b : ℕ}
    {ha : 528 ≤ a} {hb : 481 ≤ b} {v : SecretExpansionViews s}
    (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support) :
    v.shared.h128 = v.background.h128 ∧
    ∀ (x : List Bool) (i : ℕ), (481 ≤ i ∨ ∀ j : Fin (s.params.ℓ + s.params.k),
      x ≠ Keccak.bytesToBitsLE (nonceInput v.secretSeed.toList j.val)) →
      v.shared.h256.byteAt x i = v.background.h256.byteAt x i := by
  obtain ⟨T, _, M, _, seed, _, rows, _, rfl⟩ := (by
    simpa only [Xofs.sampleSecretExpansionViews, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] using hv)
  constructor
  · rfl
  · intro x i apart
    change byteAt (install base.h256 (Function.extend _ rows T)) x i =
      byteAt (install base.h256 T) x i
    simp only [byteAt_install]
    split
    next h =>
      apply Function.extend_apply'
      rintro ⟨p, hp⟩
      rcases apart with late | miss
      · have same : p.2.val = i := congrArg (fun v => v.2.val) hp
        exact (Nat.not_lt.mpr late) (same ▸ p.2.isLt)
      · apply miss (finSumFinEquiv p.1)
        exact (word_inj (hx := (length_nonceInput_bits _ _).le.trans ha) (hy := h.1)
          (congrArg Prod.fst hp)).symm
    next => rfl

/-- A pure-mode representative can coincide with a private expansion address only on the empty
message and empty context. In that case the public-key hash must equal the private seed and the
little-endian nonce must be zero. -/
theorem representativeInput_eq_nonceInput_iff (tr r : FixedBytes 64)
    (ctx : List Byte) (msg : List Bool) (j : Fin 65536) :
    representativeInput tr.toList (formatMessage msg ctx) =
        Keccak.bytesToBitsLE (nonceInput r.toList j.val) ↔
      tr = r ∧ ctx = [] ∧ msg = [] ∧ j = 0 := by
  constructor
  · intro eq
    have len := congrArg List.length eq
    rw [length_nonceInput_bits] at len
    have trLen : tr.toList.length = 64 := FixedBytes.length_toList tr
    simp only [representativeInput, formatMessage, List.length_append,
      Keccak.length_bytesToBitsLE, trLen, List.length_cons] at len
    obtain rfl : ctx = [] := List.length_eq_zero_iff.mp (by lia)
    obtain rfl : msg = [] := List.length_eq_zero_iff.mp (by lia)
    have bs : nonceInput tr.toList 0 = nonceInput r.toList j.val := by
      apply Keccak.bytesToBitsLE_injective
      apply Eq.trans _ eq
      simp only [representativeInput, formatMessage, List.append_nil]
      exact List.flatMap_append
    have seeds := congrArg (List.take 64) bs
    simp only [nonceInput, List.take_left' (FixedBytes.length_toList _)] at seeds
    obtain rfl : tr = r := List.ofFn_inj.mp seeds
    have count := eq_of_nonceInput_eq (by decide : 0 < 65536) j.isLt bs
    exact ⟨rfl, rfl, rfl, Fin.ext count.symm⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp only [representativeInput, formatMessage, List.append_nil]
    exact List.flatMap_append.symm

/-- All honest pure-mode representative reads agree outside the single potential
public-key-hash collision for the empty request. The equality is pointwise in the message and
context on the two sampled XOFs. -/
theorem SecretExpansionViews.representative_of_mem {base : Xofs} {s : Level} {a b : ℕ}
    {ha : 528 ≤ a} {hb : 481 ≤ b} {v : SecretExpansionViews s}
    (hv : v ∈ (base.sampleSecretExpansionViews s ha hb).support)
    (tr : FixedBytes 64) (ctx : List Byte) (msg : List Bool)
    (away : tr ≠ v.secretSeed ∨ ctx ≠ [] ∨ msg ≠ []) :
    v.shared.representativeFromTr tr.toList (formatMessage msg ctx) =
      v.background.representativeFromTr tr.toList (formatMessage msg ctx) := by
  apply congrArg Keccak.bytesToBitsLE
  apply read_eq_of_byteAt_eq
  intro i _
  apply (agree_of_mem hv).2 _ i
  right
  intro j hit
  have bound : s.params.ℓ + s.params.k ≤ 65536 := by cases s <;> decide
  let n := j.castLE bound
  obtain ⟨htr, hc, hm, _⟩ :=
    (representativeInput_eq_nonceInput_iff tr v.secretSeed ctx msg n).mp hit
  rcases away with h | h | h
  · exact h htr
  · exact h hc
  · exact h hm

end Cslib.Crypto.MLDSA.FIPS204
