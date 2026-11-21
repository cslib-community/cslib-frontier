/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXofMatrix
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Primitives.ByteString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformExtend
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PMFSwap

/-!
# Coupling the mask-seed reads of all signing requests to the shared SHAKE256 oracle

[FIPS 204][NISTFIPS204], Algorithm 6 line 1 derives the 32-byte private signing seed
from a 272-bit input. Algorithm 7 line 7 reads the first 64 bytes from a 1024-bit input
containing that component, a 32-byte hedge and the message representative. For distinct
hedges, all such inputs admit independent 64-byte values in the *same* raw oracle. The
quantum device can query this table before a signing request determines its representative.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability ExtendableOutput

/-- The 64-byte mask seed for each signing slot and each possible 512-bit representative. -/
abbrev SigningMaskSeeds (n : ℕ) := Fin n × BitString 512 → FixedBytes 64

private def signingSeedBytes (H : Xofs) (s : Level) (seed : FixedBytes 32) : List Byte :=
  (H.expandKeySeed s seed).drop 96

private theorem signingSeedBytes_length (H : Xofs) (s : Level) (seed : FixedBytes 32) :
    (signingSeedBytes H s seed).length = 32 := by
  simp [signingSeedBytes, Xofs.expandKeySeed, H.h256.length_read]

private def seedInput {n : ℕ} (key : List Byte) (t : Fin n ↪ FixedBytes 32)
    (p : Fin n × BitString 512) : List Bool :=
  maskSeedInput key (t p.1) (List.ofFn p.2)

private theorem seedInput_length {n : ℕ} {key : List Byte} (hk : key.length = 32)
    (t : Fin n ↪ FixedBytes 32) (p : Fin n × BitString 512) :
    (seedInput key t p).length = 1024 := by
  simp only [seedInput, length_maskSeedInput, hk, List.length_ofFn]

private theorem seedInput_injective {n : ℕ} (key : List Byte) (t : Fin n ↪ FixedBytes 32) :
    Function.Injective (seedInput key t) := by
  rintro ⟨i, μ⟩ ⟨j, ν⟩ h
  by_cases hij : i = j
  · subst j
    exact Prod.ext rfl (List.ofFn_inj.mp (List.append_cancel_left h))
  · exact (hij (t.injective (hedge_eq_of_maskSeedInput_eq h))).elim

private abbrev SeedCell (n : ℕ) := (Fin n × BitString 512) × Fin 64

private abbrev seedBytes (n : ℕ) := (Equiv.curry (Fin n × BitString 512) (Fin 64) Byte).symm

private def seedCells {n a b : ℕ} (t : Fin n ↪ FixedBytes 32) (key : List Byte)
    (hk : key.length = 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) : SeedCell n ↪ RawWord a × Fin b where
  toFun p := (word (seedInput key t p.1) ((seedInput_length hk t p.1).le.trans ha),
    Fin.castLE hb p.2)
  inj' := by
    rintro p q eq
    have he := word_inj (hx := (seedInput_length hk t p.1).le.trans ha)
      (hy := (seedInput_length hk t q.1).le.trans ha) (congrArg Prod.fst eq)
    exact Prod.ext (seedInput_injective key t he) (Fin.ext (congrArg (fun z => z.2.val) eq))

private theorem seedCells_eq {a b n : ℕ} (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a)
    (hb : 64 ≤ b) {k l : List Byte} {hk : k.length = 32} {hl : l.length = 32} (h : k = l) :
    seedCells t k hk ha hb = seedCells t l hl ha hb := by subst l; rfl

/-- Two joint raw XOF pairs. The background supplies the ordinary byte table. The shared pair
uses the supplied mask seeds at the selected Algorithm 7 addresses. -/
structure SigningMaskSeedOracles where
  /-- The pair before installing the selected seed values. -/
  background : Xofs
  /-- The pair exposed to both the forger and the honest algorithms in the exact coupling. -/
  shared : Xofs

private def streams {a b : ℕ} (base : Xofs) (T₁ T₂ : Table a b) : Xofs :=
  ⟨install base.h128 T₁, install base.h256 T₂⟩

private noncomputable def coupled {a b n : ℕ} (base : Xofs) (s : Level) (seed : FixedBytes 32)
    (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) (r : SeedCell n → Byte)
    (T₁ T₂ : Table a b) : SigningMaskSeedOracles :=
  let H := streams base T₁ T₂
  let e := seedCells t (signingSeedBytes H s seed) (signingSeedBytes_length H s seed) ha hb
  ⟨H, streams base T₁ (Function.extend e r T₂)⟩

/-- Sample raw SHAKE tables, derive the private key component at the Algorithm 6 input, then
install the supplied 64-byte values for every slot and every possible message representative.
The experiment retains both the background oracle and the shared signing oracle. -/
noncomputable def Xofs.sampleSigningMaskSeeds (base : Xofs) (s : Level) (seed : FixedBytes 32)
    {a b n : ℕ} (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (rows : SigningMaskSeeds n) : PMF SigningMaskSeedOracles := do
  let T₁ ← PMF.uniformOfFintype (Table a b)
  let T₂ ← PMF.uniformOfFintype (Table a b)
  return coupled base s seed t ha hb (seedBytes n rows) T₁ T₂

private theorem coupled_off {a b n : ℕ} (base : Xofs) (s : Level) (seed : FixedBytes 32)
    (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) (r : SeedCell n → Byte)
    (T₁ T₂ : Table a b) (x : List Bool) (i : ℕ)
    (miss : 64 ≤ i ∨ ∀ p, seedInput (signingSeedBytes (streams base T₁ T₂) s seed) t p ≠ x) :
    let pair := coupled base s seed t ha hb r T₁ T₂
    pair.shared.h256.byteAt x i = pair.background.h256.byteAt x i := by
  dsimp only [coupled, streams]
  simp only [byteAt_install]
  by_cases inside : x.length ≤ a ∧ i < b
  · simp only [dite_eq_left inside]
    apply Function.extend_apply'
    rintro ⟨p, hp⟩
    rcases miss with offset | raw
    · have eq : p.2.val = i := congrArg (fun z => z.2.val) hp
      exact (Nat.not_lt_of_ge offset) (eq ▸ p.2.isLt)
    · apply raw p.1
      apply word_inj (hx := (seedInput_length (signingSeedBytes_length ..) t p.1).le.trans ha)
        (hy := inside.1)
      exact congrArg Prod.fst hp
  · simp [inside]

private theorem coupled_key {a b n : ℕ} (base : Xofs) (s : Level) (seed : FixedBytes 32)
    (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) (r : SeedCell n → Byte)
    (T₁ T₂ : Table a b) :
    let pair := coupled base s seed t ha hb r T₁ T₂
    pair.shared.expandKeySeed s seed = pair.background.expandKeySeed s seed := by
  let pair := coupled base s seed t ha hb r T₁ T₂
  let x := keySeedInput s seed
  change pair.shared.h256.read x 128 = pair.background.h256.read x 128
  have len : x.length = 272 := length_keySeedInput s seed
  apply read_eq_of_byteAt_eq
  intro i _
  apply coupled_off _ _ _ _ _ _ _ _ _ _ _ (.inr _)
  intro p eq
  have he := congrArg List.length eq
  rw [seedInput_length (signingSeedBytes_length ..), len] at he
  contradiction

/-- Algorithm 7 reads exactly the assigned mask seed at each programmed address. The private
key component in that address is derived on the shared XOF through Algorithm 6. -/
theorem read_of_mem_sampleSigningMaskSeeds {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {pair : SigningMaskSeedOracles}
    (h : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (i : Fin n) (μ : BitString 512) :
    pair.shared.h256.read (maskSeedInput ((pair.shared.expandKeySeed s seed).drop 96)
      (t i) (List.ofFn μ)) 64 = (rows (i, μ)).toList := by
  simp only [Xofs.sampleSigningMaskSeeds, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨T₁, _, T₂, _, rfl⟩ := h
  rw [coupled_key]
  let H := streams base T₁ T₂
  let key := signingSeedBytes H s seed
  let x := seedInput key t (i, μ)
  let e := seedCells t key (signingSeedBytes_length H s seed) ha hb
  let G := install base.h256 (Function.extend e (seedBytes n rows) T₂)
  change G.read x 64 = _
  apply List.ext_getElem
  · rw [G.length_read, FixedBytes.length_toList]
  · intro j hj _
    have small : j < 64 := hj.trans_le (G.length_read ..).le
    let c : SeedCell n := ((i, μ), ⟨j, small⟩)
    have hx : x.length ≤ a := (seedInput_length (signingSeedBytes_length ..) ..).le.trans ha
    have loc : e c = (word x hx, ⟨j, small.trans_le hb⟩) := rfl
    rw [getElem_read _ _ small]
    simp only [G, byteAt_install, dite_eq_left (And.intro hx (small.trans_le hb)), ← loc,
      e.injective.extend_apply, FixedBytes.toList, List.getElem_ofFn]
    rfl

/-- Exactly where the coherent oracles can differ: SHAKE128 agrees everywhere, and SHAKE256
agrees after byte 63 and at every other raw input. The key in the selected addresses can be
read from the background oracle before installing the rows. -/
theorem agree_off_sampleSigningMaskSeeds {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {pair : SigningMaskSeedOracles}
    (h : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support) :
    pair.shared.h128 = pair.background.h128 ∧ ∀ x j,
      (64 ≤ j ∨ ∀ (i : Fin n) (μ : BitString 512),
        maskSeedInput ((pair.background.expandKeySeed s seed).drop 96) (t i) (List.ofFn μ) ≠ x) →
      pair.shared.h256.byteAt x j = pair.background.h256.byteAt x j := by
  simp only [Xofs.sampleSigningMaskSeeds, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨T₁, _, T₂, _, rfl⟩ := h
  refine ⟨rfl, fun x j miss => coupled_off _ _ _ _ _ _ _ _ _ _ _ ?_⟩
  exact miss.imp_right fun m p => m p.1 p.2

private theorem read_ne_maskSeed_length {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {pair : SigningMaskSeedOracles}
    (h : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (x : List Bool) (hx : x.length ≠ 1024) (k : ℕ) :
    pair.shared.h256.read x k = pair.background.h256.read x k := by
  apply read_eq_of_byteAt_eq
  intro j _
  apply (agree_off_sampleSigningMaskSeeds h).2 _ _ (.inr _)
  intro i μ eq
  apply hx
  rw [← eq, length_maskSeedInput, List.length_ofFn]
  change 8 * ((signingSeedBytes pair.background s seed).length + 32) + 512 = 1024
  rw [signingSeedBytes_length]

/-- The original and the shared oracles produce identical FIPS key bytes, including on
key-generation failures. The setup seed here can be chosen independently of the one used to
locate the installed rows. -/
theorem keyGen_eq_of_mem_sampleSigningMaskSeeds {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {pair : SigningMaskSeedOracles}
    (h : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (level : Level) (setup : FixedBytes 32) :
    pair.shared.keyGen level setup = pair.background.keyGen level setup := by
  have bytes (x : List Byte) (k : ℕ) (hx : x.length ≠ 128) :
      pair.shared.h256.readBytes x k = pair.background.h256.readBytes x k := by
    apply read_ne_maskSeed_length h
    rw [Keccak.length_bytesToBitsLE]
    lia
  apply Xofs.keyGen_congr_of_reads level setup (agree_off_sampleSigningMaskSeeds h).1
  · exact bytes _ _ (by simp [FixedBytes.toList])
  · intro i
    apply bytes
    simp [nonceInput, Xofs.expandKeySeed, pair.background.h256.length_read]
  · intro x hx
    apply bytes
    rw [hx]
    cases level <;> decide

private theorem publicKeyHash_eq_of_mem_sampleSigningMaskSeeds
    {base : Xofs} {s : Level} {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32}
    {ha : 1024 ≤ a} {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    {keys : KeyPair} (hg : p.background.keyGen s seed = some keys) :
    p.shared.h256.readBytes keys.publicKey 64 = p.background.h256.readBytes keys.publicKey 64 := by
  have shared := (keyGen_eq_of_mem_sampleSigningMaskSeeds hp s seed).trans hg
  obtain ⟨_, _, _, _, dec, _⟩ := privateKey_of_keyGen shared
  obtain ⟨_, _, _, _, dbg, _⟩ := privateKey_of_keyGen hg
  exact congrArg PrivateKey.tr (Option.some.inj (dec.symm.trans dbg))

private theorem sample_streams (base : Xofs) (a b : ℕ) :
    ((PMF.uniformOfFintype (Table a b)).bind fun T₁ =>
      (PMF.uniformOfFintype (Table a b)).map (streams base T₁)) = base.uniformPrefixes a b := by
  rw [independent_tables]
  exact PMF.bind_comm _ _ _

/-- For each supplied seed table, the background oracle is still the original random XOF pair. -/
theorem Xofs.background_sampleSigningMaskSeeds (base : Xofs) (s : Level) (seed : FixedBytes 32)
    {a b n : ℕ} (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (rows : SigningMaskSeeds n) :
    (base.sampleSigningMaskSeeds s seed t ha hb rows).map SigningMaskSeedOracles.background =
      base.uniformPrefixes a b := by
  rw [← sample_streams]
  simp only [sampleSigningMaskSeeds, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.pure_map]
  rfl

/-- Resampling all selected Algorithm 7 seeds at once preserves the law of the complete
shared raw oracle for each fixed key-generation seed and each fixed injective hedge tape. -/
theorem Xofs.uniform_shared_sampleSigningMaskSeeds (base : Xofs) (s : Level) (seed : FixedBytes 32)
    {a b n : ℕ} (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) :
    ((PMF.uniformOfFintype (SigningMaskSeeds n)).bind fun rows =>
      (base.sampleSigningMaskSeeds s seed t ha hb rows).map SigningMaskSeedOracles.shared) =
      base.uniformPrefixes a b := by
  rw [← sample_streams]
  simp only [sampleSigningMaskSeeds, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.pure_map]
  pmf_swap with T₁
  let e (T₂ : Table a b) := seedCells t (signingSeedBytes (streams base T₁ T₂) s seed)
    (signingSeedBytes_length ..) ha hb
  have stable (f : Table a b) (r : SeedCell n → Byte) : e (Function.extend (e f) r f) = e f := by
    let f' := Function.extend (e f) r f
    have key : signingSeedBytes (streams base T₁ f') s seed =
        signingSeedBytes (streams base T₁ f) s seed :=
      congrArg (List.drop 96) (coupled_key base s seed t ha hb r T₁ f)
    change seedCells t _ _ ha hb = seedCells t _ _ ha hb
    exact seedCells_eq t ha hb key
  let finish := fun f : Table a b => PMF.pure (streams base T₁ f)
  have law := PMF.uniformOfFintype_bind_bind_adaptiveExtend e stable finish
  rw [← PMF.uniformOfFintype_map_equiv (seedBytes n)] at law
  simp only [PMF.bind_map, Function.comp_def] at law
  rw [PMF.bind_comm]
  exact law

/-- A changed representative identifies both halves of the public-key hash as the private
signing seed `K` followed by one of the selected hedges. -/
private theorem seed_hedge_of_representative_ne {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {pair : SigningMaskSeedOracles}
    (hp : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (tr : List Byte) (ht : tr.length = 64) (formatted : List Bool)
    (hne : pair.shared.representativeFromTr tr formatted ≠
      pair.background.representativeFromTr tr formatted) :
    ∃ i, tr = (pair.background.expandKeySeed s seed).drop 96 ++ (t i).toList := by
  let key := signingSeedBytes pair.background s seed
  have hk : key.length = 32 := signingSeedBytes_length ..
  by_contra! miss
  apply hne
  apply congrArg Keccak.bytesToBitsLE
  apply read_eq_of_byteAt_eq
  intro j _
  apply (agree_off_sampleSigningMaskSeeds hp).2 _ _ (.inr _)
  intro i μ eq
  have sameLength : (Keccak.bytesToBitsLE (key ++ (t i).toList)).length =
      (Keccak.bytesToBitsLE tr).length := by
    rw [Keccak.length_bytesToBitsLE, Keccak.length_bytesToBitsLE, List.length_append,
      FixedBytes.length_toList, ht, hk]
  have bytes : key ++ (t i).toList = tr :=
    Keccak.bytesToBitsLE_injective (List.append_inj eq sameLength).1
  exact miss i bytes.symm

/-- For each setup seed and supplied table of mask seeds, with a uniformly drawn injective
hedge tape, the chance that installing the mask seeds changes the message representative for
*any* formatted input under the generated key is at most `n / 2^256`. This covers messages
chosen after any number of signing replies or measurements. -/
theorem Xofs.prob_representative_ne_sampleSigningMaskSeeds (base : Xofs) (s : Level)
    (seed : FixedBytes 32) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (hn : n ≤ 2 ^ 256) (rows : SigningMaskSeeds n) :
    letI : Nonempty (Fin n ↪ FixedBytes 32) := QuantumSigningForger.hedgeEmbedding_nonempty hn
    (((PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)).bind fun t =>
      base.sampleSigningMaskSeeds s seed t ha hb rows).toOuterMeasure
        {pair | ∃ keys, pair.background.keyGen s seed = some keys ∧ ∃ formatted,
          pair.shared.messageRepresentative keys.publicKey formatted ≠
            pair.background.messageRepresentative keys.publicKey formatted}).toReal ≤
      (n : ℝ) / 2 ^ 256 := by
  classical
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := QuantumSigningForger.hedgeEmbedding_nonempty hn
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
  let draw := fun t => base.sampleSigningMaskSeeds s seed t ha hb rows
  let bad (p : SigningMaskSeedOracles) := ∃ keys, p.background.keyGen s seed = some keys ∧
    ∃ formatted, p.shared.messageRepresentative keys.publicKey formatted ≠
      p.background.messageRepresentative keys.publicKey formatted
  let hit (H : Xofs) (t : Fin n ↪ FixedBytes 32) := ∃ keys, H.keyGen s seed = some keys ∧
    ∃ i, (t i).toList = (H.h256.readBytes keys.publicKey 64).drop 32
  let report (H : Xofs) (t : Fin n ↪ FixedBytes 32) := PMF.pure (decide (hit H t))
  change ((tapes.bind draw).toOuterMeasure {p | bad p}).toReal ≤ _
  rw [← PMF.bind_pure_decide_apply_true, PMF.bind_bind]
  apply (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) (by positivity)).mp
  calc
    _ ≤ (tapes.bind fun t => (base.uniformPrefixes a b).bind fun H => report H t) true := by
      apply PMF.bind_apply_mono_on_support
      intro t _
      rw [← base.background_sampleSigningMaskSeeds s seed t ha hb rows, PMF.bind_map]
      apply PMF.map_true_mono
      intro p hp hbad
      obtain ⟨keys, hg, formatted, ne⟩ := of_decide_eq_true hbad
      rw [Xofs.messageRepresentative, publicKeyHash_eq_of_mem_sampleSigningMaskSeeds hp hg] at ne
      apply decide_eq_true
      obtain ⟨i, eq⟩ := seed_hedge_of_representative_ne hp _ (p.background.h256.length_read ..) _ ne
      refine ⟨keys, hg, i, ?_⟩
      change p.background.h256.readBytes keys.publicKey 64 =
        signingSeedBytes p.background s seed ++ (t i).toList at eq
      rw [eq]
      simpa only [signingSeedBytes_length] using
        (List.drop_left (l₁ := signingSeedBytes p.background s seed) (l₂ := (t i).toList)).symm
    _ ≤ _ := by
      rw [PMF.bind_comm]
      apply PMF.bind_apply_le_on_support
      intro H _
      change (tapes.bind fun t => PMF.pure (decide (hit H t))) true ≤ _
      rw [PMF.bind_pure_decide_apply_true]
      cases hg : H.keyGen s seed with
      | none => simp [hit, hg]
      | some keys =>
        let tr := H.h256.readBytes keys.publicKey 64
        have ht : tr.length = 64 := H.h256.length_read ..
        obtain ⟨target, htarget⟩ := FixedBytes.exists_toList
          (show (tr.drop 32).length = 32 by simp [ht])
        have eq : {t | hit H t} = {t : Fin n ↪ FixedBytes 32 | target ∈ Set.range t} := by
          ext t
          simp only [Set.mem_ofPred_eq, hit, hg, Option.some.injEq, exists_eq_left',
            Set.mem_range, ← show tr = H.h256.readBytes keys.publicKey 64 from rfl, ← htarget,
            FixedBytes.toList, List.ofFn_inj]
        rw [eq, ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity),
          prob_uniformOfFintype_embedding_mem_range]
        simp only [Fintype.card_fin, QuantumSigningForger.card_hedge, Nat.cast_pow, Nat.cast_ofNat,
          le_refl]

namespace QuantumSigningForger

private noncomputable def withMaskSeedOracles {α : Type} (s : Level) (base : Xofs) {a b n : ℕ}
    (ha : 1024 ≤ a) (hb : 64 ≤ b) (hsize : n ≤ 2 ^ 256)
    (run : (Fin n ↪ FixedBytes 32) → FixedBytes 32 → SigningMaskSeedOracles → PMF α) : PMF α :=
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  do
    let t ← PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
    let seed ← PMF.uniformOfFintype (FixedBytes 32)
    let rows ← PMF.uniformOfFintype (SigningMaskSeeds n)
    let pair ← base.sampleSigningMaskSeeds s seed t ha hb rows
    run t seed pair

/-- The two mask-seed experiments for the signed-game comparison. Key generation uses the
background table, and the signer and scorer use the shared table. With `deviceSeesRows = true`
the device reads the shared table. With `false` it reads the background throughout its execution.
The same setup seed and tape determine the installed addresses and the actual signing run. -/
noncomputable def maskSeedGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (_hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (deviceSeesRows : Bool) (score : SignedMatrixTrial s → Bool) : Game :=
  withMaskSeedOracles s base ha hb hsize fun t seed pair =>
    C.scoreWithSetup s (if deviceSeesRows then pair.shared else pair.background)
      pair.shared (pair.background.keyGen s seed) (List.ofFn t) score

/-- Installing all mask-seed rows before the adaptive quantum interaction preserves the entire
signed-trial event law of the distinct-hedge game. This is the shared-device side of the
comparison with a background-only device. -/
theorem shared_maskSeedGame_eq_distinctHedgeGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (score : SignedMatrixTrial s → Bool) :
    C.maskSeedGame s base ha hb hn hsize true score =
      C.distinctHedgeGame s base a b hn hsize score := by
  simp only [maskSeedGame, withMaskSeedOracles, distinctHedgeGame, fixedHedgeGame,
    PMF.monad_bind_eq_bind, ↓reduceIte]
  congr 1
  funext t
  rw [PMF.bind_comm (base.uniformPrefixes a b)]
  congr 1
  funext seed
  let run := fun H => C.scoreWithSetup s H H (H.keyGen s seed) (List.ofFn t) score
  have law := congrArg (PMF.bind · run) (base.uniform_shared_sampleSigningMaskSeeds s seed t ha hb)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at law
  refine Eq.trans ?_ (law.trans (by congr 1))
  congr 1
  funext rows
  refine PMF.bind_congr_on_support _ _ _ fun pair hp => ?_
  dsimp only [run]
  rw [keyGen_eq_of_mem_sampleSigningMaskSeeds hp s seed]

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
