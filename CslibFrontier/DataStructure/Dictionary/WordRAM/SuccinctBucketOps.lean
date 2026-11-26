/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.WramOmega

/-!
# Bucket-Level Dictionary Lookup and Insertion (`query`, `insert`) in `Memory.Prog`

This module defines the bucket-level representation invariant `BucketStateInv` and realizes the
bucket-level lookup and insertion operations of the fixed-capacity succinct dictionary in
`Memory.Prog` via `realize`:
* `BucketStateInv`: couples `SlotStoreInv`, `AllChainsValid`, indexed micro-chain membership,
  per-bucket quotient uniqueness, and the abstract per-bucket quotient-to-value map `B`;
* `queryBodyProg_bucket_spec`: lookup correctness and probe-excess cost bound under
  `BucketStateInv`;
* `insertBodyProg` and `realizes_insertBodyGen`: bucket-level `insert` (update in-place if present,
  otherwise append to bucket and prepend to micro-chain if `< effBucketCap n_max`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.BucketStateInv`: bucket-level representation
  invariant coupling `SlotStoreInv`, `AllChainsValid`, and the abstract per-bucket map `B`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertBodyProg`: `Memory.Prog` operation for
  bucket-level insertion (`update` in place if present, otherwise `pushBackSlotProg` +
  `prependIfIndexedProg`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.bucketStateInv_of_zero`: an all-zero dictionary
  memory region satisfies `BucketStateInv` with empty buckets and zero potential.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg_bucket_spec`: lookup correctness
  and probe-excess `memoryCost` bound for `queryBodyProg` under `BucketStateInv`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertBodyProg_bucket_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_insertBodyGen`: insertion correctness,
  `BucketStateInv` preservation, amortized `memoryCost` bound, and `Realizes` certificate for
  `insertBodyProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: `BucketStateInv` and `queryBodyProg_bucket_spec` -/

/-- Combined bucket-level state invariant at `base` with local micro-bucket mapping `mOf : ℕ → ℕ`,
per-bucket micro-chain lists `L : ℕ → ℕ → List ℕ`, and abstract per-bucket quotient-to-value map
`B : ℕ → ℕ → Option ℕ`. -/
structure BucketStateInv (U V w₀ n_max h_space base : ℕ)
    (mOf : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (B : ℕ → ℕ → Option ℕ) (s : Memory.State) : Prop where
  hslot : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem)
  hchains : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s.mem) L
  hchain_mem : ∀ b < numBuckets n_max, ∀ m < numMicroPerBucket n_max, ∀ j,
    j ∈ L b m ↔
      j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b ∧
      j < effBucketCap n_max ∧
      mOf (quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j)) = m
  hnodup_q : ∀ b < numBuckets n_max,
    ∀ j₁ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    ∀ j₂ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₁) =
    quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₂) →
    j₁ = j₂
  hmap_some : ∀ b < numBuckets n_max,
    ∀ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    B b (quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j)) =
    some (valAt base U V w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j))
  hmap_dom : ∀ b < numBuckets n_max, ∀ q,
    (B b q).isSome ↔
      ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
        quotAt base U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q

/-- An all-zero dictionary memory region satisfies `BucketStateInv` with empty chains and empty
bucket maps. -/
theorem bucketStateInv_of_zero {U V w₀ n_max h_space base : ℕ} (mOf : ℕ → ℕ)
    {s : Memory.State}
    (hgm0 : ∀ i, gmAt base U V w₀ n_max h_space s.mem i = 0)
    (hlm0 : ∀ p, lmAt base U V w₀ n_max h_space s.mem p = 0) :
    BucketStateInv U V w₀ n_max h_space base mOf (fun _ _ => []) (fun _ _ => none) s ∧
    totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) = 0 ∧
    slotPotential n_max (gmAt base U V w₀ n_max h_space s.mem) = 0 := by
  obtain ⟨hslot, hbc0, hpot0⟩ := slotStoreInv_of_zero n_max hgm0
  exact ⟨⟨hslot, allChainsValid_of_zero n_max hlm0,
    fun b _ m _ j => by simp [hbc0 b],
    fun b _ j₁ hj₁ => by simp [hbc0 b] at hj₁,
    fun b _ j hj => by simp [hbc0 b] at hj,
    fun b _ q => by simp [hbc0 b]⟩,
    totalSlots_of_zero n_max hgm0, hpot0⟩

/-- `BucketStateInv` implies `SearchMicroChainPre` for any valid `(b, q_target, m)`. -/
theorem BucketStateInv.searchMicroChainPre {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    SearchMicroChainPre U V w₀ n_max h_space w (((base, b), q_target), m) s :=
  ⟨henv, hb, hm, hinv.hslot, L b m, hinv.hchains.1 b hb m hm,
    fun j hj => ((hinv.hchain_mem b hb m hm j).mp hj).1⟩

/-- Under `BucketStateInv` and `m = mOf q_target < numMicroPerBucket n_max`, the two-phase search
condition in `searchBucketProg_spec` is equivalent to
`∃ j < bCount b, quotAt (slotOf b j) = q_target`. -/
theorem searchBucket_exists_iff {U V w₀ n_max h_space base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    ((∃ j ∈ L b m, quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target) ∨
     (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm b ∧
        quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target)) ↔
    (∃ j < bCount n_max gm b,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target) := by
  intro gm
  refine ⟨?_, fun ⟨j, hj_lt, hq⟩ => ?_⟩
  · rintro (⟨j, hj_in, hq⟩ | ⟨j, _, hj_lt, hq⟩)
    · exact ⟨j, ((hinv.hchain_mem b hb m hm_lt j).mp hj_in).1, hq⟩
    · exact ⟨j, hj_lt, hq⟩
  · rcases lt_or_ge j (effBucketCap n_max) with hj_cap | hj_ge
    · exact Or.inl ⟨j, (hinv.hchain_mem b hb m hm_lt j).mpr ⟨hj_lt, hj_cap, hq ▸ hm_eq.symm⟩, hq⟩
    · exact Or.inr ⟨j, hj_ge, hj_lt, hq⟩

/-- Found flag (`1` if present, `0` if absent) in a `searchBucketProg` result
`((found, j_found), phys)`. -/
abbrev searchResFound (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.1

/-- Bucket-local slot index `j_found` in a `searchBucketProg` result
`((found, j_found), phys)`. -/
abbrev searchResIdx (res : (ℕ × ℕ) × ℕ) : ℕ := res.1.2

/-- Specification of `searchBucketProg` under `BucketStateInv` when `m = mOf q_target`. -/
theorem searchBucketProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := searchBucketProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      10 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j < bCount n_max gm b,
         quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target then
       searchResFound res = 1 ∧
       searchResIdx res < bCount n_max gm b ∧
       quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b (searchResIdx res)) = q_target ∧
       res.2 = slotOf n_max gm b (searchResIdx res)
     else
       searchResFound res = 0) := by
  intro gm d prog
  have ⟨hst, hcost, hres⟩ := searchBucketProg_spec henv hb hm_lt hinv.hslot
    (hinv.hchains.1 b hb m hm_lt) (fun j hj => ((hinv.hchain_mem b hb m hm_lt j).mp hj).1) (d := d)
  refine ⟨hst, hcost, ?_⟩
  have hiff := searchBucket_exists_iff hinv hb hm_eq hm_lt
  dsimp only [d, gm, prog, ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfSearchFound,
    ovfSearchIdx] at hres hiff ⊢
  split_ifs with hex
  · rw [ite_eq_left (hiff.mpr hex)] at hres
    exact ⟨hres.1, hres.2.1, hres.2.2.2.1, hres.2.2.2.2⟩
  · rwa [ite_eq_right (mt hiff.mp hex)] at hres

/-- Specification of `queryBodyProg` under `BucketStateInv` when `m = mOf q_target`:
returns `B b q_target` without modifying memory. -/
theorem queryBodyProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := queryBodyProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      12 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    (Memory.spec 0).clientResult s prog = B b q_target := by
  intro gm d prog
  have ⟨hst, hcost, hres⟩ := queryBodyProg_spec henv hb hm_lt hinv.hslot
    (hinv.hchains.1 b hb m hm_lt) (fun j hj => ((hinv.hchain_mem b hb m hm_lt j).mp hj).1) (d := d)
  refine ⟨hst, hcost, ?_⟩
  dsimp only [d, gm, prog, ovfQueryBase, ovfQueryBucket, ovfQueryQuot] at hres ⊢
  split_ifs at hres with hex
  · rcases hres with ⟨j, hj_lt, rfl, hres_eq⟩
    exact hres_eq.trans (hinv.hmap_some b hb j hj_lt).symm
  · have hno : ¬(B b q_target).isSome := fun hs =>
      hex ((searchBucket_exists_iff hinv hb hm_eq hm_lt).mpr ((hinv.hmap_dom b hb q_target).mp hs))
    exact hres.trans (Option.not_isSome_iff_eq_none.mp hno).symm

/-! ## Section 2: `insertBodyProg` via `realize` -/

/-- Base address `d.1.1.1` of a bucket-level dictionary call `(((base, b), x), y)`. -/
abbrev bucketCallBase {α β : Type} (d : ((ℕ × ℕ) × α) × β) : ℕ := d.1.1.1

/-- Bucket index `d.1.1.2` of a bucket-level dictionary call `(((base, b), x), y)`. -/
abbrev bucketCallBucket {α β : Type} (d : ((ℕ × ℕ) × α) × β) : ℕ := d.1.1.2

/-- Base-and-bucket pair `(base, b)` of a bucket-level dictionary call `(((base, b), x), y)`. -/
abbrev bucketCallPair {α β : Type} (d : ((ℕ × ℕ) × α) × β) : ℕ × ℕ := d.1.1

/-- Base address `d.1.1.1.1` of a nested bucket-level call `((((base, b), x), y), z)`. -/
abbrev nestedCallBase {α β γ : Type} (d : (((ℕ × ℕ) × α) × β) × γ) : ℕ := d.1.1.1.1

/-- Bucket index `d.1.1.1.2` of a nested bucket-level call `((((base, b), x), y), z)`. -/
abbrev nestedCallBucket {α β γ : Type} (d : (((ℕ × ℕ) × α) × β) × γ) : ℕ := d.1.1.1.2

/-- Base-and-bucket pair `(base, b)` of a nested bucket-level call `((((base, b), x), y), z)`. -/
abbrev nestedCallPair {α β γ : Type} (d : (((ℕ × ℕ) × α) × β) × γ) : ℕ × ℕ := d.1.1.1

/-- Target quotient `q_target` in an insertion input `((((base, b), q_target), v_new), m)`. -/
abbrev insertArgQuot (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- Query prefix `((base, b), q_target)` in an insertion input
`((((base, b), q_target), v_new), m)`. -/
abbrev insertArgQuery (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : (ℕ × ℕ) × ℕ := d.1.1

/-- Inserted value `v_new` in an insertion input `((((base, b), q_target), v_new), m)`. -/
abbrev insertArgVal (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Micro-bucket index `m` in an insertion input `((((base, b), q_target), v_new), m)`. -/
abbrev insertArgMicro (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : ℕ := d.2

/-- Parameter-free helper `Memory.Prog` appending a new `(q_target, v_new)` entry to bucket `b` and
prepending its logical index `j_new = bCount b` to micro-chain `(b, m)` when `totalSlots < n_max`.
Input `d = (dp, ((((base, b), q_target), v_new), m))`. -/
@[expose]
def insertNewGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let tot ← readTotalSlotsGenProg (d.1, nestedCallBase d.2)
  let cap ← pure (dpNMax d.1)
  if tot < cap then do
    let j_new ← readBucketCountGenProg (d.1, nestedCallPair d.2)
    pushBackSlotGenProg (((d.1, nestedCallPair d.2), insertArgQuot d.2), insertArgVal d.2)
    prependIfIndexedGenProg ((d.1, (nestedCallPair d.2, insertArgMicro d.2)), j_new)
  else
    pure ()

/-- Helper `Memory.Prog` appending a new `(q_target, v_new)` entry to bucket `b` and prepending
its logical index `j_new = bCount b` to micro-chain `(b, m)` when `totalSlots < n_max`.
Input `d = ((((base, b), q_target), v_new), m)`. -/
@[expose]
def insertNewProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  insertNewGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem insertNewGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    insertNewGenProg (mkDictParams U V w n_max h_space, d) =
      insertNewProg U V w n_max h_space d := by
  rfl

/-- Precondition for `insertNewProg` in `Realizes`. -/
@[expose]
def InsertNewPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) (nestedCallBase d) ∧
  nestedCallBucket d < numBuckets n_max ∧
  insertArgMicro d < numMicroPerBucket n_max ∧
  insertArgQuot d < 2 ^ quotientBits U n_max ∧
  insertArgVal d < 2 ^ valBits V ∧
  SlotStoreInv n_max (gmAt (nestedCallBase d) U V w₀ n_max h_space s.mem) ∧
  lmHead n_max (lmAt (nestedCallBase d) U V w₀ n_max h_space s.mem)
    (nestedCallBucket d) (insertArgMicro d) ≤ effBucketCap n_max

/-- Parameter-free precondition for `insertNewGenProg` in `Realizes`. -/
@[expose]
def InsertNewGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 (nestedCallBase d.2) ∧
  nestedCallBucket d.2 < numBuckets (dpNMax d.1) ∧
  insertArgMicro d.2 < numMicroPerBucket (dpNMax d.1) ∧
  insertArgQuot d.2 < 2 ^ quotientBits (dpU d.1) (dpNMax d.1) ∧
  insertArgVal d.2 < 2 ^ valBits (dpV d.1) ∧
  SlotStoreInv (dpNMax d.1)
    (gmAt (nestedCallBase d.2) (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
  lmHead (dpNMax d.1)
    (lmAt (nestedCallBase d.2) (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    (nestedCallBucket d.2) (insertArgMicro d.2) ≤ effBucketCap (dpNMax d.1)

@[simp]
theorem insertNewGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    InsertNewGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      InsertNewPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_insertNewGen :
    Realizes .exact insertNewGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      InsertNewGenPre
      (fun _ _ => 0) := by
  realizeDictWith [insertNewGenPre_mk, InsertNewPre, readTotalSlotsGenProg_mk,
    pushBackSlotGenPre_mk, PushBackSlotPre, pushBackSlotGenProg_mk,
    prependIfIndexedGenPre_mk, PrependIfIndexedPre, prependIfIndexedGenProg_mk,
    nestedCallBase, nestedCallBucket, nestedCallPair, insertArgQuot, insertArgVal,
    insertArgMicro] using
    [realizes_readTotalSlotsGen, realizes_readBucketCountGen, realizes_pushBackSlotGen,
      realizes_prependIfIndexedGen]
  · exact h.1
  · exact h.2.2.2.2.2.1
  · exact h.1
  · rw [clientState_readTotalSlotsProg]; exact h.2.2.2.2.2.1
  · exact h.2.1
  · rw [clientState_readTotalSlotsProg, clientState_readBucketCountProg]
    rw [clientResult_readTotalSlotsProg] at hc
    exact ⟨h.1, h.2.2.2.2.2.1, h.2.1, hc, h.2.2.2.1, h.2.2.2.2.1⟩
  · rw [clientState_readTotalSlotsProg, clientState_readBucketCountProg]
    rw [clientResult_readTotalSlotsProg] at hc
    have eff := pushBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (q_val := d.1.1.2)
      (v_val := d.1.2) hw s h.2.2.2.2.2.1 h.2.1 hc h.2.2.2.1 h.2.2.2.2.1
    exact ⟨h.1, h.2.1, h.2.2.1, by rw [eff.2.2.1]; exact h.2.2.2.2.2.2⟩

/-- Parameter-free dictionary `insert` body `insertBodyGenProg`
(`d = (dp, ((((base, b), q_target), v_new), m))`). -/
@[expose]
def insertBodyGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let res ← searchBucketGenProg (d.1, (insertArgQuery d.2, insertArgMicro d.2))
  let z1 ← pure 1
  if searchResFound res = z1 then
    writeValGenProg (d.1, ((nestedCallBase d.2, res.2), insertArgVal d.2))
  else
    insertNewGenProg d

/-- Dictionary `insert` body `insertBodyProg` (`d = ((((base, b), q_target), v_new), m)`):
searches bucket `b` for `q_target` via `searchBucketProg`; if found, overwrites `valAt` in-place;
otherwise calls `insertNewProg`. -/
@[expose]
def insertBodyProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  insertBodyGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem insertBodyGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    insertBodyGenProg (mkDictParams U V w n_max h_space, d) =
      insertBodyProg U V w n_max h_space d := by
  rfl

/-- Precondition for `insertBodyProg` in `Realizes`. -/
@[expose]
def InsertBodyPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  SearchMicroChainPre U V w₀ n_max h_space w (insertArgQuery d, insertArgMicro d) s ∧
  insertArgQuot d < 2 ^ quotientBits U n_max ∧
  insertArgVal d < 2 ^ valBits V

/-- Parameter-free precondition for `insertBodyGenProg` in `Realizes`. -/
@[expose]
def InsertBodyGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  SearchMicroChainGenPre w (d.1, (insertArgQuery d.2, insertArgMicro d.2)) s ∧
  insertArgQuot d.2 < 2 ^ quotientBits (dpU d.1) (dpNMax d.1) ∧
  insertArgVal d.2 < 2 ^ valBits (dpV d.1)

@[simp]
theorem insertBodyGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    InsertBodyGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      InsertBodyPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_insertBodyGen :
    Realizes .exact insertBodyGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      InsertBodyGenPre
      (fun _ _ => 0) := by
  realize [realizes_searchBucketGen, realizes_writeValGen, realizes_insertNewGen]
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1.1
    simpDictParamsWith [insertBodyGenPre_mk, InsertBodyPre,
      searchMicroChainGenPre_mk, SearchMicroChainPre, searchBucketGenProg_mk,
      insertNewGenPre_mk, InsertNewPre, insertNewGenProg_mk,
      nestedCallBase, insertArgQuery, insertArgQuot, insertArgVal, insertArgMicro,
      searchResFound]
  )
  · exact h.1
  · exact fits_const_of_dictEnv h.1.1 (by decide)
  · exact h.1.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.1.2.2.2.2
    have hspec := (searchBucketProg_spec (d := (d.1.1, d.2))
      h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 hchain hc_lt).2.2
    dsimp only [ovfSearchFound, ovfSearchIdx] at hspec
    split_ifs at hspec with hex
    · rw [hspec.2.2.2.2]
      exact (slotOf_lt_and_injective h.1.2.2.2.1).1 d.1.1.1.2 h.1.2.1 _ hspec.2.1
    · omega
  · obtain ⟨L, hchain, hc_lt⟩ := h.1.2.2.2.2
    rw [(searchBucketProg_spec (d := (d.1.1, d.2))
      h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2.1, h.2.2, h.1.2.2.2.1, hchain.head_le_cap⟩

/-- Updating `valAt` in place at slot `slotOf b j₀` updates `B b q_target` to `some v_new`. -/
private theorem bucketStateInv_updateVal {U V w₀ n_max h_space base b j₀ q_target v_new : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s s' : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max)
    (hj₀ : j₀ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)
    (hq₀ : quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₀) = q_target)
    (hgm : gmAt base U V w₀ n_max h_space s'.mem = gmAt base U V w₀ n_max h_space s.mem)
    (hlm : lmAt base U V w₀ n_max h_space s'.mem = lmAt base U V w₀ n_max h_space s.mem)
    (hq : quotAt base U w₀ n_max h_space s'.mem = quotAt base U w₀ n_max h_space s.mem)
    (hv : valAt base U V w₀ n_max h_space s'.mem =
      Function.update (valAt base U V w₀ n_max h_space s.mem)
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₀) v_new) :
    BucketStateInv U V w₀ n_max h_space base mOf L
      (Function.update B b (Function.update (B b) q_target (some v_new))) s' := by
  have hinj := (slotOf_lt_and_injective hinv.hslot).2
  refine ⟨by rw [hgm]; exact hinv.hslot, hinv.hchains.of_lm_eq hlm,
    fun b' hb' m' hm' j => by rw [hgm, hq]; exact hinv.hchain_mem b' hb' m' hm' j,
    fun b' hb' j₁ hj₁ j₂ hj₂ => by
      rw [hgm] at hj₁ hj₂; rw [hgm, hq]; exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂,
    fun b' hb' j hj => ?_, fun b' hb' q => ?_⟩
  · rw [hgm] at hj; rw [hgm, hq, hv]
    rcases eq_or_ne b' b with rfl | hbeq
    · rcases eq_or_ne j j₀ with rfl | hjeq
      · simp [hq₀]
      · have hq_ne : quotAt base U w₀ n_max h_space s.mem
            (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j) ≠ q_target :=
          fun heq => hjeq (hinv.hnodup_q b' hb' j hj j₀ hj₀ (heq.trans hq₀.symm))
        have hs_ne : slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j ≠
            slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j₀ :=
          fun heq => hjeq (hinj b' hb' j hj b' hb' j₀ hj₀ heq).2
        simp [hq_ne, hs_ne, hinv.hmap_some b' hb' j hj]
    · have hs_ne : slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j ≠
          slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₀ :=
        fun heq => hbeq (hinj b' hb' j hj b hb j₀ hj₀ heq).1
      simp [hbeq, hs_ne, hinv.hmap_some b' hb' j hj]
  · rw [hgm, hq]
    rcases eq_or_ne b' b with rfl | hbeq
    · rcases eq_or_ne q q_target with rfl | hqeq
      · simpa using ⟨j₀, hj₀, hq₀⟩
      · simp [hqeq, hinv.hmap_dom b' hb' q]
    · simp [hbeq, hinv.hmap_dom b' hb' q]

/-- Appending a fresh `(q_target, v_new)` to bucket `b` and prepending its index `j_new` into
micro-chain `(b, m)` when indexed preserves `BucketStateInv`. -/
private theorem bucketStateInv_pushBack
    {U V w₀ n_max h_space base b q_target v_new m : ℕ}
    {mOf : ℕ → ℕ} {L L' : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s s' : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (habs : ¬∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target)
    (hslot' : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s'.mem))
    (hchains' : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s'.mem) L')
    (hbc_b : bCount n_max (gmAt base U V w₀ n_max h_space s'.mem) b =
      bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b + 1)
    (hbc_other : ∀ b' < numBuckets n_max, b' ≠ b →
      bCount n_max (gmAt base U V w₀ n_max h_space s'.mem) b' =
        bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b')
    (hq_new : quotAt base U w₀ n_max h_space s'.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b
        (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)) = q_target)
    (hv_new : valAt base U V w₀ n_max h_space s'.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b
        (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)) = v_new)
    (hold : ∀ b' < numBuckets n_max,
      ∀ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b',
      quotAt base U w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b' j) =
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j) ∧
      valAt base U V w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b' j) =
      valAt base U V w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j))
    (hmem' : ∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max, ∀ j,
      j ∈ L' b' m' ↔
        j ∈ L b' m' ∨
        (b' = b ∧ m' = m ∧ j = bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b ∧
          bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b < effBucketCap n_max)) :
    BucketStateInv U V w₀ n_max h_space base mOf L'
      (Function.update B b (Function.update (B b) q_target (some v_new))) s' := by
  let j_new := bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b
  refine ⟨hslot', hchains',
    fun b' hb' m' hm' j => ?_, fun b' hb' j₁ hj₁ j₂ hj₂ hq_eq => ?_,
    fun b' hb' j hj => ?_, fun b' hb' q => ?_⟩
  · rw [hmem' b' hb' m' hm' j, hinv.hchain_mem b' hb' m' hm' j]
    rcases eq_or_ne b' b with rfl | hbeq
    · rw [hbc_b]
      rcases eq_or_ne j j_new with rfl | hjeq
      · simp [j_new, hq_new, ← hm_eq, and_comm, eq_comm]
      · simp only [show j ≠ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' from hjeq,
          false_and, and_false, or_false]
        exact ⟨fun ⟨hj, hcap, hm_j⟩ => ⟨by omega, hcap, (hold b' hb' j hj).1.symm ▸ hm_j⟩,
          fun ⟨hj, hcap, hm_j⟩ => ⟨by omega, hcap, (hold b' hb' j (by omega)).1 ▸ hm_j⟩⟩
    · simp only [hbeq, false_and, or_false]
      rw [hbc_other b' hb' hbeq]
      exact and_congr_right fun hj => by simp [(hold b' hb' j hj).1]
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [hbc_b] at hj₁ hj₂
      wlog hle : j₁ ≤ j₂ generalizing j₁ j₂
      · exact (this j₂ hj₂ j₁ hj₁ hq_eq.symm (by omega)).symm
      rcases eq_or_ne j₂ j_new with rfl | h2
      · by_contra h1
        have hj1 : j₁ < j_new := by omega
        exact habs ⟨j₁, hj1, ((hold b' hb' j₁ hj1).1.symm.trans hq_eq).trans hq_new⟩
      · have hj1 : j₁ < j_new := by omega
        have hj2 : j₂ < j_new := by omega
        rw [(hold b' hb' j₁ hj1).1, (hold b' hb' j₂ hj2).1] at hq_eq
        exact hinv.hnodup_q b' hb' j₁ hj1 j₂ hj2 hq_eq
    · rw [hbc_other b' hb' hbeq] at hj₁ hj₂
      rw [(hold b' hb' j₁ hj₁).1, (hold b' hb' j₂ hj₂).1] at hq_eq
      exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂ hq_eq
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [hbc_b] at hj
      rcases eq_or_ne j j_new with rfl | hjeq
      · simp [j_new, hq_new, hv_new]
      · have hj_lt : j < j_new := by omega
        rw [(hold b' hb' j hj_lt).1, (hold b' hb' j hj_lt).2]
        have hq_ne : _ ≠ q_target := fun heq => habs ⟨j, hj_lt, heq⟩
        simp [hq_ne, hinv.hmap_some b' hb' j hj_lt]
    · rw [hbc_other b' hb' hbeq] at hj
      rw [(hold b' hb' j hj).1, (hold b' hb' j hj).2]
      simp [hbeq, hinv.hmap_some b' hb' j hj]
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [Function.update_self, hbc_b]
      rcases eq_or_ne q q_target with rfl | hqeq
      · simpa using ⟨j_new, le_rfl, hq_new⟩
      · rw [Function.update_of_ne hqeq, hinv.hmap_dom b' hb' q]
        refine ⟨fun ⟨j, hj, hq⟩ => ⟨j, by omega, (hold b' hb' j hj).1.trans hq⟩,
          fun ⟨j, hj, hq⟩ => ?_⟩
        rcases eq_or_ne j j_new with rfl | hjeq
        · exact absurd (hq.symm.trans hq_new) hqeq
        · have hj_lt : j < j_new := by omega
          exact ⟨j, hj_lt, (hold b' hb' j hj_lt).1.symm.trans hq⟩
    · rw [Function.update_of_ne hbeq, hbc_other b' hb' hbeq, hinv.hmap_dom b' hb' q]
      exact exists_congr fun j => and_congr_right fun hj => by simp [(hold b' hb' j hj).1]

/-- Pure state effect, `BucketStateInv` preservation, and amortized `memoryCost` bound of
`insertNewProg` when `q_target` is absent from bucket `b` and `totalSlots < n_max`. -/
private theorem insertNewProg_bucket_spec
    {U V w₀ n_max h_space base b q_target v_new m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max)
    (hq_lt : q_target < 2 ^ quotientBits U n_max) (hv_lt : v_new < 2 ^ valBits V)
    (htot : totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) < n_max)
    (habs : ¬∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let d := ((((base, b), q_target), v_new), m)
    let s' := (Memory.spec 0).clientState s (insertNewProg U V w₀ n_max h_space d)
    let gm' := gmAt base U V w₀ n_max h_space s'.mem
    let B' := Function.update B b (Function.update (B b) q_target (some v_new))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
    (∃ L', BucketStateInv U V w₀ n_max h_space base mOf L' B' s') ∧
    totalSlots n_max gm' = totalSlots n_max gm₀ + 1 ∧
    memoryCost (insertNewProg U V w₀ n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 160 := by
  intro gm₀ d s' gm' B'
  let j_new := bCount n_max gm₀ b
  let s₁ := (Memory.spec 0).clientState s
    (pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new))
  have eff_pb := pushBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
    (h_space := h_space) (base := base) (b := b) (q_val := q_target) (v_val := v_new)
    hw s hinv.hslot hb htot hq_lt hv_lt
  rcases eff_pb with ⟨hf_pb, hout_pb, hlm_pb, hslot₁, htot₁, hbc_b₁, hbc_o₁,
    hq_new₁, hv_new₁, hold₁, hcost_pb⟩
  have hj_lt_n : j_new < n_max := lt_of_le_of_lt (bCount_le_totalSlots hinv.hslot b hb) htot
  have hj_not : ∀ m' < numMicroPerBucket n_max, j_new ∉ L b m' := fun m' hm' h =>
    Nat.lt_irrefl _ ((hinv.hchain_mem b hb m' hm' j_new).mp h).1
  have eff_pr := prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
    (h_space := h_space) (base := base) (b := b) (m := m) (j_new := j_new)
    hw hb hm_lt hj_lt_n (hinv.hchains.of_lm_eq hlm_pb) hj_not
  rcases eff_pr with ⟨hf_pr, hout_pr, hq_pr, hv_pr, hgm_pr, L', hchains', hmem'⟩
  have hs' : s' = (Memory.spec 0).clientState s₁
      (prependIfIndexedProg U V w₀ n_max h_space (((base, b), m), j_new)) := by
    simp only [s', d, insertNewProg, insertNewGenProg, readTotalSlotsGenProg_mk, p_nMax_mk,
      readBucketCountGenProg_mk, pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readTotalSlotsProg,
      clientResult_readTotalSlotsProg, ite_eq_left htot, StateTransitionSpec.clientState_bind,
      clientState_readBucketCountProg, clientResult_readBucketCountProg (base, b) s hb,
      StateTransitionSpec.clientState_bind]
  have hcost_in : memoryCost (insertNewProg U V w₀ n_max h_space d) s ≤
      26 + memoryCost (pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new)) s := by
    simp only [d, insertNewProg, insertNewGenProg, readTotalSlotsGenProg_mk, p_nMax_mk,
      readBucketCountGenProg_mk, pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk,
      nestedCallBase, nestedCallPair, insertArgQuot, insertArgVal, insertArgMicro,
      pure_bind, ← PFunctor.FreeM.bind_eq_bind]
    rw [memoryCost_bind, clientState_readTotalSlotsProg, clientResult_readTotalSlotsProg,
      ite_eq_left htot, memoryCost_bind, clientState_readBucketCountProg,
      clientResult_readBucketCountProg (base, b) s hb, memoryCost_bind]
    have hc_tot := memoryCost_readTotalSlotsProg_le U V w₀ n_max h_space base s
    have hc_bc := memoryCost_readBucketCountProg_le (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base, b) s
    have hc_pr := memoryCost_prependIfIndexedProg_le U V w₀ n_max h_space (((base, b), m), j_new) s₁
    dsimp only [s₁, j_new, gm₀] at hc_pr ⊢
    omega
  rw [← hs'] at hf_pr hout_pr hq_pr hv_pr hgm_pr hchains'
  rw [← hgm_pr] at hslot₁ htot₁ hbc_b₁ hbc_o₁ hq_new₁ hv_new₁ hold₁ hcost_pb
  rw [← hq_pr] at hq_new₁
  rw [← hv_pr] at hv_new₁
  exact ⟨hf_pr.trans hf_pb,
    fun a ha => (hout_pr a (by wram_omega [ha])).trans (hout_pb a ha),
    ⟨L', bucketStateInv_pushBack hinv hb hm_eq habs hslot₁ hchains' hbc_b₁ hbc_o₁
      hq_new₁ hv_new₁
      (fun b' hb' j hj => by simpa only [hq_pr, hv_pr] using hold₁ b' hb' j hj)
      hmem'⟩,
    htot₁, by dsimp only [gm', gm₀] at hcost_in hcost_pb ⊢; omega⟩

/-- Pure state effect, `BucketStateInv` preservation, and amortized `memoryCost` bound of
`insertBodyProg` when `m = mOf q_target` and `(B b q_target).isSome ∨ totalSlots < n_max`. -/
theorem insertBodyProg_bucket_spec {U V w₀ n_max h_space w base b q_target v_new m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max)
    (hq_lt : q_target < 2 ^ quotientBits U n_max)
    (hv_lt : v_new < 2 ^ valBits V)
    (hcap : (B b q_target).isSome ∨
      totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) < n_max) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let d := ((((base, b), q_target), v_new), m)
    let s' := (Memory.spec 0).clientState s (insertBodyProg U V w₀ n_max h_space d)
    let gm' := gmAt base U V w₀ n_max h_space s'.mem
    let B' := Function.update B b (Function.update (B b) q_target (some v_new))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
    (∃ L', BucketStateInv U V w₀ n_max h_space base mOf L' B' s') ∧
    totalSlots n_max gm' =
      (if (B b q_target).isSome then totalSlots n_max gm₀ else totalSlots n_max gm₀ + 1) ∧
    memoryCost (insertBodyProg U V w₀ n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 170 +
        8 * (L b m).length + 6 * (bCount n_max gm₀ b - effBucketCap n_max) := by
  intro gm₀ d s' gm' B'
  have ⟨hsb_st, hsb_cost, hres⟩ :=
    searchBucketProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  dsimp only [s', gm', gm₀, d] at *
  simp only [insertBodyProg, insertBodyGenProg, searchBucketGenProg_mk, writeValGenProg_mk,
    insertNewGenProg_mk, pure_bind]
  rw [StateTransitionSpec.clientState_bind, memoryCost_bind_of_clientState_eq hsb_st, hsb_st]
  by_cases hex : ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
  · rw [ite_eq_left hex] at hres
    rcases hres with ⟨hf1, hj_lt, hq_match, hphys_eq⟩
    have hsome : (B b q_target).isSome := (hinv.hmap_dom b hb q_target).mpr hex
    have hphys_lt : _ < n_max := hphys_eq ▸ (slotOf_lt_and_injective hinv.hslot).1 b hb _ hj_lt
    have eff := writeValProg_effect (U := U) (base := base) (h_space := h_space)
      hw hphys_lt hv_lt s
    rw [ite_eq_left hf1, ite_eq_left hsome, memoryCost_writeValProg, eff.2.2.2.2.2]
    exact ⟨eff.1, fun a ha => eff.2.1 a (by wram_omega [ha]),
      ⟨L, bucketStateInv_updateVal hinv hb hj_lt hq_match eff.2.2.2.2.2 eff.2.2.2.2.1
        eff.2.2.1 (hphys_eq ▸ eff.2.2.2.1)⟩,
      rfl, by omega⟩
  · rw [ite_eq_right hex] at hres
    have hnot_some : ¬(B b q_target).isSome := mt (hinv.hmap_dom b hb q_target).mp hex
    have hne1 : searchResFound ((Memory.spec 0).clientResult s
        (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m))) ≠ 1 := by omega
    have hnew := insertNewProg_bucket_spec hw hinv hb hm_eq hm_lt hq_lt hv_lt
      (hcap.resolve_left hnot_some) hex
    rw [ite_eq_right hne1, ite_eq_right hnot_some]
    exact ⟨hnew.1, hnew.2.1, hnew.2.2.1, hnew.2.2.2.1, by omega⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
