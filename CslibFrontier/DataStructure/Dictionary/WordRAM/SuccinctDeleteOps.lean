/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctBucketOps
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.WramOmega

/-!
# Bucket-Level Dictionary Deletion (`deletePrepProg`, `deleteFinishProg`) in `Memory.Prog`

This module realizes the two-phase bucket-level deletion of the fixed-capacity succinct dictionary
in `Memory.Prog` via `realize`:
* `deletePrepProg` and `realizes_deletePrepGen`: Phase 1 of `delete` (search bucket `b` for
  `q_target` and, if found, read the quotient `q_last` of the last slot in the bucket so that the
  Word-RAM wrapper can compute `m_last`);
* `deleteSwapProg`, `deleteFoundProg`, `deleteFinishProg`, and `realizes_deleteFinishGen`: Phase 2
  of `delete` (unlink the deleted slot, swap the last slot into the deleted slot and relink into
  `m_last` when `j_del < j_last`, and pop the last slot from the bucket).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deletePrepProg`: Phase 1 of `delete` in
  `Memory.Prog` (searches bucket `b` and reads `q_last` when found).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteSwapProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFoundProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFinishProg`: Phase 2 of `delete` in
  `Memory.Prog` (unlinks `j_del`, relocates `j_last` into `j_del` when `j_del < j_last`, and calls
  `popBackSlotProg`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_deletePrepGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deletePrepProg_bucket_spec`: `Realizes`
  certificate and bucket-level specification for `deletePrepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_deleteFinishGen`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFinishProg_bucket_spec`: `Realizes`
  certificate, `BucketStateInv` preservation, and amortized `memoryCost` bound for
  `deleteFinishProg`.
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

/-! ## Section 1: `deletePrepProg` via `realize` -/

/-- Parameter-free Phase 1 of `delete` (`d = (dp, (((base, b), q_target), m))`):
searches bucket `b` for `q_target`; if found (`searchResFound res = 1`), resolves the last slot
`phys_last` of bucket `b`, reads its quotient `q_last`, and returns `(res, q_last)`; otherwise
returns `(((0, 0), 0), 0)`. -/
@[expose]
def deletePrepGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let res ← searchBucketGenProg d
  let z1 ← pure 1
  if searchResFound res = z1 then do
    let phys_last ← lastSlotOfGenProg (d.1, bucketCallPair d.2)
    let q_last ← readQuotGenProg (d.1, (bucketCallBase d.2, phys_last))
    pure (res, q_last)
  else do
    let z0 ← pure 0
    pure (((z0, z0), z0), z0)

/-- Phase 1 of `delete` (`d = (((base, b), q_target), m)`):
searches bucket `b` for `q_target`; if found (`res.1.1 = 1`), resolves the last slot `phys_last` of
bucket `b`, reads its quotient `q_last`, and returns `(res, q_last)`; otherwise returns
`(((0, 0), 0), 0)`. -/
@[expose]
def deletePrepProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) :=
  deletePrepGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem deletePrepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    deletePrepGenProg (mkDictParams U V w n_max h_space, d) =
      deletePrepProg U V w n_max h_space d := by
  rfl

/-- When `searchBucketProg` reports `found = 1`, the returned logical index is `< bCount`, so
`1 ≤ bCount`. -/
private theorem searchBucketProg_found_imp_pos_bCount {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (h : SearchMicroChainPre U V w₀ n_max h_space w d s)
    (hfound :
      ((Memory.spec 0).clientResult s (searchBucketProg U V w₀ n_max h_space d)).1.1 = 1) :
    1 ≤ bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 := by
  obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
  have hres := (searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).2.2
  dsimp only [ovfQueryBase, ovfQueryBucket, ovfQueryQuot, ovfSearchFound, ovfSearchIdx] at hres
  split_ifs at hres
  · have := hres.2.1; omega
  · omega

theorem realizes_deletePrepGen :
    Realizes .exact deletePrepGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre, lmEntryBase, lmEntryBucket,
    searchBucketGenProg_mk, lastSlotOfGenPre_mk, lastSlotOfGenProg_mk, searchResFound,
    bucketCallBase, bucketCallPair] using
    [realizes_searchBucketGen, realizes_lastSlotOfGen, realizes_readQuotGen]
  · exact h
  · exact fits_const_of_dictEnv h.1 (by decide)
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1, h.2.2.2.1, h.2.1, searchBucketProg_found_imp_pos_bCount h hc⟩
  · exact h.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    rw [(searchBucketProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).1]
    have hbc := searchBucketProg_found_imp_pos_bCount h hc
    rw [clientResult_lastSlotOfProg d.1.1 s h.2.2.2.1 h.2.1 hbc]
    exact (slotOf_lt_and_injective h.2.2.2.1).1 d.1.1.2 h.2.1 _ (by omega)

/-- Search header `(found, j_del)` in a `deletePrepProg` result
`(((found, j_del), phys_del), q_last)`. -/
abbrev deletePrepHdr (prep : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ × ℕ := prep.1.1

/-- Found flag (`1` if found, `0` otherwise) in a `deletePrepProg` result
`(((found, j_del), phys_del), q_last)`. -/
abbrev deletePrepFound (prep : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := prep.1.1.1

/-- Bucket-local slot index `j_del` in a `deletePrepProg` result
`(((found, j_del), phys_del), q_last)`. -/
abbrev deletePrepIdx (prep : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := prep.1.1.2

/-- Physical slot `phys_del` in a `deletePrepProg` result
`(((found, j_del), phys_del), q_last)`. -/
abbrev deletePrepPhys (prep : ((ℕ × ℕ) × ℕ) × ℕ) : ℕ := prep.1.2

/-- Specification of `deletePrepProg` under `BucketStateInv` when `m = mOf q_target`. -/
theorem deletePrepProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := deletePrepProg U V w₀ n_max h_space d
    let prep := (Memory.spec 0).clientResult s prog
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      16 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    prep.2 < 2 ^ quotientBits U n_max ∧
    (if ∃ j < bCount n_max gm b,
         quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target then
       deletePrepFound prep = 1 ∧
       deletePrepIdx prep < bCount n_max gm b ∧
       quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b (deletePrepIdx prep)) = q_target ∧
       deletePrepPhys prep = slotOf n_max gm b (deletePrepIdx prep) ∧
       prep.2 = quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b (bCount n_max gm b - 1))
     else
       deletePrepFound prep = 0 ∧ prep.2 = 0) := by
  intro gm d prog prep
  dsimp only [d, prog, prep, deletePrepFound, deletePrepIdx, deletePrepPhys]
  have ⟨hsb_st, hsb_cost, hres⟩ :=
    searchBucketProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  dsimp only at hsb_st hsb_cost hres
  simp only [deletePrepProg, deletePrepGenProg, searchBucketGenProg_mk, lastSlotOfGenProg_mk,
    readQuotGenProg_mk, bucketCallBase, bucketCallPair, pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    memoryCost_bind_of_clientState_eq hsb_st, hsb_st]
  set res := (Memory.spec 0).clientResult s
    (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m))
  by_cases hex : ∃ j < bCount n_max gm b,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target
  · rw [ite_eq_left hex] at hres
    rcases hres with ⟨hf1, hj_lt, hq_match, hphys_eq⟩
    have hbc : 1 ≤ bCount n_max gm b := by dsimp only [gm] at *; omega
    have hlast_lt : slotOf n_max gm b (bCount n_max gm b - 1) < n_max :=
      (slotOf_lt_and_injective hinv.hslot).1 b hb _ (by dsimp only [gm] at *; omega)
    rw [ite_eq_left hf1, ite_eq_left hex, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq (clientState_lastSlotOfProg ..), clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (base, b) s hinv.hslot hb hbc,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      memoryCost_bind_of_clientState_eq (clientState_readQuotProg ..), clientState_readQuotProg,
      clientResult_readQuotProg s hlast_lt, memoryCost_readQuotProg, memoryCost_pure]
    have hc2 := memoryCost_lastSlotOfProg_le U V w₀ n_max h_space (base, b) s
    exact ⟨rfl, by dsimp only [gm] at *; omega, quotAt_lt base U w₀ n_max h_space s.mem _,
      hf1, hj_lt, hq_match, hphys_eq, rfl⟩
  · rw [ite_eq_right hex] at hres
    rw [ite_eq_right (show searchResFound res ≠ 1 by omega), ite_eq_right hex, memoryCost_pure]
    exact ⟨rfl, by dsimp only [gm] at *; omega, Nat.two_pow_pos _, rfl, rfl⟩

/-! ## Section 2: `deleteSwapProg`, `deleteFoundProg`, and `deleteFinishProg` via `realize` -/

/-- Logical index `j_del` of the deleted slot in `((((base, b), j_del), phys_del), extra)`. -/
abbrev deleteSlotIdx {α : Type} (d : (((ℕ × ℕ) × ℕ) × ℕ) × α) : ℕ := d.1.1.2

/-- Physical slot `phys_del` of the deleted slot in `((((base, b), j_del), phys_del), extra)`. -/
abbrev deleteSlotPhys {α : Type} (d : (((ℕ × ℕ) × ℕ) × ℕ) × α) : ℕ := d.1.2

/-- Target slot descriptor `(((base, b), j_del), phys_del)` in a delete-slot input. -/
abbrev deleteSlotTarget {α : Type} (d : (((ℕ × ℕ) × ℕ) × ℕ) × α) : ((ℕ × ℕ) × ℕ) × ℕ := d.1

/-- Micro-bucket `m_last` of the relocated last slot in a `deleteSwapProg` input. -/
abbrev deleteSwapMicro (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Logical index `j_last` of the relocated last slot in a `deleteSwapProg` input. -/
abbrev deleteSwapLastIdx (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Parameter-free swap helper for `delete` when `j_del < j_last`
(`d = (dp, ((((base, b), j_del), phys_del), (m_last, j_last)))`). -/
@[expose]
def deleteSwapGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) : Memory.Prog Unit := do
  unlinkIfIndexedGenProg ((d.1, (nestedCallPair d.2, deleteSwapMicro d.2)), deleteSwapLastIdx d.2)
  copyLastPayloadGenProg (d.1, (nestedCallPair d.2, deleteSlotPhys d.2))
  prependIfIndexedGenProg ((d.1, (nestedCallPair d.2, deleteSwapMicro d.2)), deleteSlotIdx d.2)

/-- Swap helper for `delete` when `j_del < j_last`
(`d = ((((base, b), j_del), phys_del), (m_last, j_last))`):
unlinks `j_last` from `(b, m_last)` (if indexed), copies `(q_last, v_last)` into `phys_del`, and
prepends `j_del` to `(b, m_last)` (if indexed). -/
@[expose]
def deleteSwapProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit :=
  deleteSwapGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem deleteSwapGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) :
    deleteSwapGenProg (mkDictParams U V w n_max h_space, d) =
      deleteSwapProg U V w n_max h_space d := by
  rfl

theorem memoryCost_deleteSwapProg_le (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (deleteSwapProg U V w n_max h_space d) s ≤ 50 := by
  simp only [deleteSwapProg, deleteSwapGenProg, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk,
    nestedCallPair, deleteSwapMicro, deleteSwapLastIdx, deleteSlotPhys, deleteSlotIdx,
    ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2))
  have h1 := memoryCost_unlinkIfIndexedProg_le U V w n_max h_space ((d.1.1.1, d.2.1), d.2.2) s
  have h2 := memoryCost_copyLastPayloadProg_le U V w n_max h_space (d.1.1.1, d.1.2) s₁
  have h3 := memoryCost_prependIfIndexedProg_le U V w n_max h_space ((d.1.1.1, d.2.1), d.1.1.2)
    ((Memory.spec 0).clientState s₁ (copyLastPayloadProg U V w n_max h_space (d.1.1.1, d.1.2)))
  dsimp only [s₁] at h2 h3
  omega

/-- Precondition for `deleteSwapProg` in `Realizes`. -/
@[expose]
def DeleteSwapPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := nestedCallBase d
  let b := nestedCallBucket d
  let m_last := deleteSwapMicro d
  let j_last := deleteSwapLastIdx d
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem) ∧
  b < numBuckets n_max ∧
  m_last < numMicroPerBucket n_max ∧
  1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b ∧
  deleteSlotPhys d < n_max ∧
  j_last < n_max ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid n_max (lmAt base U V w₀ n_max h_space s.mem) L ∧
    (j_last < effBucketCap n_max → j_last ∈ L b m_last)

/-- Parameter-free precondition for `deleteSwapGenProg` in `Realizes`. -/
@[expose]
def DeleteSwapGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) (s : Memory.State) : Prop :=
  let base := nestedCallBase d.2
  let b := nestedCallBucket d.2
  let m_last := deleteSwapMicro d.2
  let j_last := deleteSwapLastIdx d.2
  let gm := gmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  let lm := lmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 base ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  b < numBuckets (dpNMax d.1) ∧
  m_last < numMicroPerBucket (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm b ∧
  deleteSlotPhys d.2 < dpNMax d.1 ∧
  j_last < dpNMax d.1 ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid (dpNMax d.1) lm L ∧
    (j_last < effBucketCap (dpNMax d.1) → j_last ∈ L b m_last)

@[simp]
theorem deleteSwapGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    DeleteSwapGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteSwapPre U V w₀ n_max h_space w d s := Iff.rfl

/-- `AllChainsValid` gives the `UnlinkIfIndexedPre` neighbour bounds for an indexed member `j`. -/
private theorem unlinkIfIndexedPre_of_allChainsValid {U V w₀ n_max h_space w base b m j : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hval : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s.mem) L)
    (hmem_if : j < effBucketCap n_max → j ∈ L b m) :
    UnlinkIfIndexedPre U V w₀ n_max h_space w (((base, b), m), j) s :=
  ⟨henv, hb, hm, fun hj =>
    ⟨(hval.1 b hb m hm).prev_le_cap (hmem_if hj), (hval.1 b hb m hm).next_le_cap (hmem_if hj)⟩⟩

theorem realizes_deleteSwapGen :
    Realizes .exact deleteSwapGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      DeleteSwapGenPre
      (fun _ _ => 0) := by
  realizeDictWith [deleteSwapGenPre_mk, DeleteSwapPre,
    unlinkIfIndexedGenPre_mk, UnlinkIfIndexedPre, unlinkIfIndexedGenProg_mk,
    copyLastPayloadGenPre_mk, CopyLastPayloadPre, copyLastPayloadGenProg_mk,
    prependIfIndexedGenPre_mk, PrependIfIndexedPre, prependIfIndexedGenProg_mk,
    nestedCallBase, nestedCallBucket, nestedCallPair, deleteSlotIdx, deleteSlotPhys,
    deleteSwapMicro, deleteSwapLastIdx] using
    [realizes_unlinkIfIndexedGen, realizes_copyLastPayloadGen, realizes_prependIfIndexedGen]
  all_goals obtain ⟨L, hval, hmem_if⟩ := h.2.2.2.2.2.2.2
  · exact unlinkIfIndexedPre_of_allChainsValid h.1 h.2.2.1 h.2.2.2.1 hval hmem_if
  all_goals
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.2.2)
      hw h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.1 hval hmem_if
  · exact ⟨h.1, by rw [eff_u.2.2.2.2.1]; exact h.2.1, h.2.2.1,
      by rw [eff_u.2.2.2.2.1]; exact h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · have eff_c := copyLastPayloadProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (phys_del := d.1.2)
      hw (by rw [eff_u.2.2.2.2.1]; exact h.2.1) h.2.2.1
      (by rw [eff_u.2.2.2.2.1]; exact h.2.2.2.2.1) h.2.2.2.2.2.1
    obtain ⟨L₁, hval₁, _⟩ := eff_u.2.2.2.2.2
    exact ⟨h.1, h.2.2.1, h.2.2.2.1,
      by rw [eff_c.2.2.2.2.1]; exact (hval₁.1 d.1.1.1.2 h.2.2.1 d.2.1 h.2.2.2.1).head_le_cap⟩

section

attribute [local irreducible] mkDictParams

/-- Pure state effect and `AllChainsValid` update of `deleteSwapProg`: unlinks `j_last`, copies the
last slot's payload into `phys_del`, and prepends `j_del` into `(b, m_last)`. -/
private theorem deleteSwapProg_effect
    {U V w₀ n_max h_space base b j_del phys_del m_last j_last : ℕ}
    {L : ℕ → ℕ → List ℕ} {s : Memory.State} (hw : 0 < w₀)
    (hslot : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem))
    (hb : b < numBuckets n_max) (hm_last : m_last < numMicroPerBucket n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)
    (hphys_del : phys_del < n_max) (hj_del : j_del < n_max) (hj_last : j_last < n_max)
    (hval : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s.mem) L)
    (hmem_last : j_last < effBucketCap n_max → j_last ∈ L b m_last)
    (hj_not : ∀ m' < numMicroPerBucket n_max, j_del ∉ L b m') :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s
      (deleteSwapProg U V w₀ n_max h_space ((((base, b), j_del), phys_del), (m_last, j_last)))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + totalSpace U V w₀ n_max h_space) →
      s'.mem a = s.mem a) ∧
    gmAt base U V w₀ n_max h_space s'.mem = gm ∧
    quotAt base U w₀ n_max h_space s'.mem =
      Function.update (quotAt base U w₀ n_max h_space s.mem) phys_del
        (quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b (bCount n_max gm b - 1))) ∧
    valAt base U V w₀ n_max h_space s'.mem =
      Function.update (valAt base U V w₀ n_max h_space s.mem) phys_del
        (valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm b (bCount n_max gm b - 1))) ∧
    ∃ L' : ℕ → ℕ → List ℕ,
      AllChainsValid n_max (lmAt base U V w₀ n_max h_space s'.mem) L' ∧
      (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max, ∀ j,
        j ∈ L' b' m' ↔
          (j ∈ L b' m' ∧ ¬(b' = b ∧ j = j_last)) ∨
          (b' = b ∧ m' = m_last ∧ j = j_del ∧ j_del < effBucketCap n_max)) := by
  intro gm s'
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w₀ n_max h_space (((base, b), m_last), j_last))
  have ⟨hf_u, hout_u, hq_u, hv_u, hgm_u, L₁, hval₁, hmem₁⟩ :=
    unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m_last) (j_del := j_last)
      (s := s) hw hb hm_last hj_last hval hmem_last
  let s₂ := (Memory.spec 0).clientState s₁
    (copyLastPayloadProg U V w₀ n_max h_space ((base, b), phys_del))
  have ⟨hf_c, hout_c, hq_c, hv_c, hlm_c, hgm_c⟩ :=
    copyLastPayloadProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (phys_del := phys_del) (s := s₁)
      hw (by rw [hgm_u]; exact hslot) hb (by rw [hgm_u]; exact hbc) hphys_del
  have hj_not₁ : ∀ m' < numMicroPerBucket n_max, j_del ∉ L₁ b m' := fun m' hm' hin =>
    hj_not m' hm' ((hmem₁ b hb m' hm' j_del).mp hin).1
  have ⟨hf_p, hout_p, hq_p, hv_p, hgm_p, L₂, hval₂, hmem₂⟩ :=
    prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m_last) (j_new := j_del)
      (s := s₂) hw hb hm_last hj_del (hval₁.of_lm_eq hlm_c) hj_not₁
  have hs' : s' = (Memory.spec 0).clientState s₂
      (prependIfIndexedProg U V w₀ n_max h_space (((base, b), m_last), j_del)) := by
    simp only [s', deleteSwapProg, deleteSwapGenProg, unlinkIfIndexedGenProg_mk,
      copyLastPayloadGenProg_mk, prependIfIndexedGenProg_mk]
    repeat rw [StateTransitionSpec.clientState_bind]
  rw [hs']
  exact ⟨by rw [hf_p, hf_c, hf_u],
    fun a ha => by
      have ha_lm : ¬(base + offLM U V w₀ n_max h_space ≤ a ∧
          a < base + offGM U V w₀ n_max h_space) := by wram_omega [ha]
      rw [hout_p a ha_lm, hout_c a ha, hout_u a ha_lm],
    by rw [hgm_p, hgm_c, hgm_u],
    by rw [hq_p, hq_c, hgm_u, hq_u],
    by rw [hv_p, hv_c, hgm_u, hv_u],
    L₂, hval₂, fun b' hb' m' hm' j => by rw [hmem₂ b' hb' m' hm' j, hmem₁ b' hb' m' hm' j]⟩

end

/-- Micro-bucket `m` of the deleted slot in a `deleteFoundProg` input. -/
abbrev deleteFoundMicro (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.1

/-- Micro-bucket `m_last` of the bucket's last slot in a `deleteFoundProg` input. -/
abbrev deleteFoundLastMicro (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : ℕ := d.2.2

/-- Parameter-free found-branch helper for `delete`
(`d = (dp, ((((base, b), j_del), phys_del), (m, m_last)))`). -/
@[expose]
def deleteFoundGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) : Memory.Prog Unit := do
  unlinkIfIndexedGenProg ((d.1, (nestedCallPair d.2, deleteFoundMicro d.2)), deleteSlotIdx d.2)
  let c_b ← readBucketCountGenProg (d.1, nestedCallPair d.2)
  let j_last ← pure (c_b - 1)
  if deleteSlotIdx d.2 < j_last then do
    deleteSwapGenProg (d.1, (deleteSlotTarget d.2, (deleteFoundLastMicro d.2, j_last)))
    popBackSlotGenProg (d.1, nestedCallPair d.2)
  else
    popBackSlotGenProg (d.1, nestedCallPair d.2)

/-- Found-branch helper for `delete` (`d = ((((base, b), j_del), phys_del), (m, m_last))`):
unlinks `j_del` from `(b, m)`, reads `c_b`, runs `deleteSwapProg` if `j_del < c_b - 1`, and
calls `popBackSlotProg`. -/
@[expose]
def deleteFoundProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog Unit :=
  deleteFoundGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem deleteFoundGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) :
    deleteFoundGenProg (mkDictParams U V w n_max h_space, d) =
      deleteFoundProg U V w n_max h_space d := by
  rfl

/-- Precondition for `deleteFoundProg` in `Realizes`. -/
@[expose]
def DeleteFoundPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := nestedCallBase d
  let b := nestedCallBucket d
  let j_del := deleteSlotIdx d
  let phys_del := deleteSlotPhys d
  let m := deleteFoundMicro d
  let m_last := deleteFoundLastMicro d
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let lm := lmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  m < numMicroPerBucket n_max ∧
  m_last < numMicroPerBucket n_max ∧
  j_del < bCount n_max gm b ∧
  phys_del < n_max ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid n_max lm L ∧
    (j_del < effBucketCap n_max → j_del ∈ L b m) ∧
    (bCount n_max gm b - 1 < effBucketCap n_max → bCount n_max gm b - 1 ∈ L b m_last)

/-- Parameter-free precondition for `deleteFoundGenProg` in `Realizes`. -/
@[expose]
def DeleteFoundGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))) (s : Memory.State) : Prop :=
  let base := nestedCallBase d.2
  let b := nestedCallBucket d.2
  let j_del := deleteSlotIdx d.2
  let phys_del := deleteSlotPhys d.2
  let m := deleteFoundMicro d.2
  let m_last := deleteFoundLastMicro d.2
  let gm := gmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  let lm := lmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 base ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  b < numBuckets (dpNMax d.1) ∧
  m < numMicroPerBucket (dpNMax d.1) ∧
  m_last < numMicroPerBucket (dpNMax d.1) ∧
  j_del < bCount (dpNMax d.1) gm b ∧
  phys_del < dpNMax d.1 ∧
  ∃ L : ℕ → ℕ → List ℕ,
    AllChainsValid (dpNMax d.1) lm L ∧
    (j_del < effBucketCap (dpNMax d.1) → j_del ∈ L b m) ∧
    (bCount (dpNMax d.1) gm b - 1 < effBucketCap (dpNMax d.1) →
      bCount (dpNMax d.1) gm b - 1 ∈ L b m_last)

@[simp]
theorem deleteFoundGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    DeleteFoundGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteFoundPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_deleteFoundGen :
    Realizes .exact deleteFoundGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      DeleteFoundGenPre
      (fun _ _ => 0) := by
  realizeDictWith [deleteFoundGenPre_mk, DeleteFoundPre,
    unlinkIfIndexedGenPre_mk, UnlinkIfIndexedPre, unlinkIfIndexedGenProg_mk,
    deleteSwapGenPre_mk, DeleteSwapPre, deleteSwapGenProg_mk,
    popBackSlotGenPre_mk, PopBackSlotPre, popBackSlotGenProg_mk,
    nestedCallBase, nestedCallBucket, nestedCallPair, deleteSlotIdx, deleteSlotPhys,
    deleteSlotTarget, deleteFoundMicro, deleteFoundLastMicro] using
    [realizes_unlinkIfIndexedGen, realizes_readBucketCountGen,
      realizes_deleteSwapGen, realizes_popBackSlotGen]
  · obtain ⟨L, hval, hmem_del, _⟩ := h.2.2.2.2.2.2.2
    exact unlinkIfIndexedPre_of_allChainsValid h.1 h.2.2.1 h.2.2.2.1 hval hmem_del
  · exact h.1
  swap
  · exact h.2.2.1
  all_goals
    obtain ⟨L, hval, hmem_del, hmem_last⟩ := h.2.2.2.2.2.2.2
    have hj_n : d.1.1.2 < n_max := lt_of_lt_of_le h.2.2.2.2.2.1 (bCount_le_n_max h.2.1 d.1.1.1.2)
    have eff_u := unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (m := d.2.1) (j_del := d.1.1.2)
      hw h.2.2.1 h.2.2.2.1 hj_n hval hmem_del
    have hbc_pos : 1 ≤ bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 := by
      have := h.2.2.2.2.2.1; omega
  · rw [eff_u.2.2.2.2.1]; exact h.2.1
  · rw [clientResult_readBucketCountProg d.1.1.1 _ h.2.2.1, eff_u.2.2.2.2.1]; exact hbc_pos
  rotate_right 1
  · rw [clientState_readBucketCountProg]
    exact ⟨h.1, by rw [eff_u.2.2.2.2.1]; exact h.2.1,
      h.2.2.1, by rw [eff_u.2.2.2.2.1]; exact hbc_pos⟩
  all_goals
    rw [clientState_readBucketCountProg]
    rw [clientResult_readBucketCountProg d.1.1.1 _ h.2.2.1, eff_u.2.2.2.2.1] at hc ⊢
    obtain ⟨L₁, hval₁, hmem₁⟩ := eff_u.2.2.2.2.2
    have hj_last_n :
        bCount n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 - 1 < n_max := by
      have := bCount_le_n_max h.2.1 d.1.1.1.2; omega
    have hmem_last₁ := fun hj_cap => (hmem₁ d.1.1.1.2 h.2.2.1 d.2.2 h.2.2.2.2.1 _).mpr
      ⟨hmem_last hj_cap, fun ⟨_, heq⟩ => by omega⟩
  · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, hbc_pos, h.2.2.2.2.2.2.1, hj_last_n,
      L₁, hval₁, hmem_last₁⟩
  · have hsw := deleteSwapProg_effect (U := U) (V := V) (w₀ := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (j_del := d.1.1.2)
      (phys_del := d.1.2) (m_last := d.2.2) (j_last := _) hw
      (by rw [eff_u.2.2.2.2.1]; exact h.2.1) h.2.2.1 h.2.2.2.2.1
      (by rw [eff_u.2.2.2.2.1]; exact hbc_pos)
      h.2.2.2.2.2.2.1 hj_n hj_last_n hval₁ hmem_last₁
      (fun m' hm' hin => ((hmem₁ d.1.1.1.2 h.2.2.1 m' hm' d.1.1.2).mp hin).2 ⟨rfl, rfl⟩)
    have hgm_sw := hsw.2.2.1.trans eff_u.2.2.2.2.1
    exact ⟨h.1, by rw [hgm_sw]; exact h.2.1, h.2.2.1, by rw [hgm_sw]; exact hbc_pos⟩

/-- Base address `base` in a `deleteFinishProg` input
`(((((base, b), (found, j_del)), phys_del), m), m_last)`. -/
abbrev deleteFinishBase (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1.1.1

/-- Base-and-bucket pair `(base, b)` in a `deleteFinishProg` input. -/
abbrev deleteFinishPair (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ × ℕ := d.1.1.1.1

/-- Found flag `found` in a `deleteFinishProg` input. -/
abbrev deleteFinishFound (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1.2.1

/-- Logical index `j_del` in a `deleteFinishProg` input. -/
abbrev deleteFinishIdx (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.1.2.2

/-- Physical slot `phys_del` in a `deleteFinishProg` input. -/
abbrev deleteFinishPhys (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ := d.1.1.2

/-- Micro-bucket `m` in a `deleteFinishProg` input. -/
abbrev deleteFinishMicro (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : ℕ := d.1.2

/-- Extract the `deleteFoundProg` input `((((base, b), j_del), phys_del), (m, m_last))` from a
`deleteFinishProg` input. -/
abbrev deleteFinishToFound (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) :
    (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) :=
  (((deleteFinishPair d, deleteFinishIdx d), deleteFinishPhys d), (deleteFinishMicro d, d.2))

/-- Parameter-free Phase 2 of `delete`
(`d = (dp, (((((base, b), (found, j_del)), phys_del), m), m_last))`). -/
@[expose]
def deleteFinishGenProg
    (d : DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let z1 ← pure 1
  if deleteFinishFound d.2 = z1 then
    deleteFoundGenProg (d.1, deleteFinishToFound d.2)
  else
    pure ()

/-- Phase 2 of `delete` (`d = ((((base, b), (found, j_del)), phys_del), m), m_last`):
if `found = 1`, calls `deleteFoundProg`; otherwise returns `()`. -/
@[expose]
def deleteFinishProg (U V w n_max h_space : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  deleteFinishGenProg (mkDictParams U V w n_max h_space, d)

@[simp]
theorem deleteFinishGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) :
    deleteFinishGenProg (mkDictParams U V w n_max h_space, d) =
      deleteFinishProg U V w n_max h_space d := by
  rfl

/-- Precondition for `deleteFinishProg` in `Realizes`. -/
@[expose]
def DeleteFinishPre (U V w₀ n_max h_space w : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) (deleteFinishBase d) ∧
  (deleteFinishFound d = 1 →
    DeleteFoundPre U V w₀ n_max h_space w (deleteFinishToFound d) s)

/-- Parameter-free precondition for `deleteFinishGenProg` in `Realizes`. -/
@[expose]
def DeleteFinishGenPre (w : ℕ)
    (d : DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 (deleteFinishBase d.2) ∧
  (deleteFinishFound d.2 = 1 →
    DeleteFoundGenPre w (d.1, deleteFinishToFound d.2) s)

@[simp]
theorem deleteFinishGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : ((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    DeleteFinishGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DeleteFinishPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_deleteFinishGen :
    Realizes .exact deleteFinishGenProg
      (WordEncoding.encode (α := DictParams × (((((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      DeleteFinishGenPre
      (fun _ _ => 0) := by
  realizeDictWith [deleteFinishGenPre_mk, DeleteFinishPre,
    deleteFoundGenPre_mk, DeleteFoundPre, deleteFoundGenProg_mk,
    deleteFinishBase, deleteFinishPair, deleteFinishFound, deleteFinishIdx,
    deleteFinishPhys, deleteFinishMicro, deleteFinishToFound] using [realizes_deleteFoundGen]
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.2 hc

section

-- All parameter projections in this section are transported by the existing specialization
-- lemmas. Keep the packed parameter constructor opaque to definitional equality: comparing
-- intermediate client states must not expand its 36-way layout-parameter match.
attribute [local irreducible] mkDictParams

/-- `deleteFoundProg` reduces to `popBackSlotProg` on an intermediate state `s_mid` whose
`GlobalMeta` agrees with `s`, whose payload in bucket `b` is remapped via
`idxMap j = if j = j_del then j_last else j`, and whose micro-chains reflect `idxMap`. -/
private theorem deleteFoundProg_prePop_spec
    {U V w₀ n_max h_space base b q_target j_del m m_last : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max)
    (hm_eq : m = mOf q_target) (hm_lt : m < numMicroPerBucket n_max)
    (hm_last_lt : m_last < numMicroPerBucket n_max)
    (hj_del_lt : j_del < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)
    (hq_del : quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j_del) = q_target)
    (hm_last_eq : m_last = mOf (quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b
        (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1)))) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let phys_del := slotOf n_max gm₀ b j_del
    let j_last := bCount n_max gm₀ b - 1
    let idxMap : ℕ → ℕ := fun j => if j = j_del then j_last else j
    let prog := deleteFoundProg U V w₀ n_max h_space
      ((((base, b), j_del), phys_del), (m, m_last))
    ∃ s_mid : Memory.State, ∃ L_mid : ℕ → ℕ → List ℕ,
      (Memory.spec 0).clientState s prog =
        (Memory.spec 0).clientState s_mid (popBackSlotProg U V w₀ n_max h_space (base, b)) ∧
      memoryCost prog s ≤
        66 + memoryCost (popBackSlotProg U V w₀ n_max h_space (base, b)) s_mid ∧
      s_mid.frontier = s.frontier ∧
      (∀ a, ¬(base + offQuot h_space ≤ a ∧
          a < base + totalSpace U V w₀ n_max h_space) → s_mid.mem a = s.mem a) ∧
      gmAt base U V w₀ n_max h_space s_mid.mem = gm₀ ∧
      (∀ b' < numBuckets n_max, b' ≠ b → ∀ j < bCount n_max gm₀ b',
        quotAt base U w₀ n_max h_space s_mid.mem (slotOf n_max gm₀ b' j) =
          quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
        valAt base U V w₀ n_max h_space s_mid.mem (slotOf n_max gm₀ b' j) =
          valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
      (∀ j < j_last,
        quotAt base U w₀ n_max h_space s_mid.mem (slotOf n_max gm₀ b j) =
          quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j)) ∧
        valAt base U V w₀ n_max h_space s_mid.mem (slotOf n_max gm₀ b j) =
          valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j))) ∧
      AllChainsValid n_max (lmAt base U V w₀ n_max h_space s_mid.mem) L_mid ∧
      (∀ b' < numBuckets n_max, b' ≠ b → ∀ m' < numMicroPerBucket n_max, ∀ j,
        j ∈ L_mid b' m' ↔ j ∈ L b' m') ∧
      (∀ m' < numMicroPerBucket n_max, ∀ j,
        j ∈ L_mid b m' ↔
          j < j_last ∧ j < effBucketCap n_max ∧
          mOf (quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j))) = m') := by
  intro gm₀ phys_del j_last idxMap prog
  have hj_last_lt : j_last < bCount n_max gm₀ b := by dsimp only [j_last, gm₀]; omega
  have hbc_pos : 1 ≤ bCount n_max gm₀ b := by dsimp only [gm₀]; omega
  have hphys_del_lt : phys_del < n_max := (slotOf_lt_and_injective hinv.hslot).1 b hb _ hj_del_lt
  have hj_del_n : j_del < n_max := lt_of_lt_of_le hj_del_lt (bCount_le_n_max hinv.hslot b)
  have hj_last_n : j_last < n_max := lt_of_lt_of_le hj_last_lt (bCount_le_n_max hinv.hslot b)
  have hmem_del : j_del < effBucketCap n_max → j_del ∈ L b m := fun hcap =>
    (hinv.hchain_mem b hb m hm_lt j_del).mpr ⟨hj_del_lt, hcap, hq_del ▸ hm_eq.symm⟩
  let s₁ := (Memory.spec 0).clientState s
    (unlinkIfIndexedProg U V w₀ n_max h_space (((base, b), m), j_del))
  have ⟨hf_u1, hout_u1, hq_u1, hv_u1, hgm_u1, L₁, hval₁, hmem₁⟩ :=
    unlinkIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (j_del := j_del)
      hw hb hm_lt hj_del_n hinv.hchains hmem_del
  have hc_u1 := memoryCost_unlinkIfIndexedProg_le U V w₀ n_max h_space (((base, b), m), j_del) s
  have hc_bc := memoryCost_readBucketCountProg_le (U := U) (V := V) (w := w₀) (n_max := n_max)
    (h_space := h_space) (base, b) s₁
  let tail := if j_del < j_last then do
    deleteSwapProg U V w₀ n_max h_space ((((base, b), j_del), phys_del), (m_last, j_last))
    popBackSlotProg U V w₀ n_max h_space (base, b)
  else popBackSlotProg U V w₀ n_max h_space (base, b)
  have hst_base : (Memory.spec 0).clientState s prog = (Memory.spec 0).clientState s₁ tail := by
    simp only [prog, tail, deleteFoundProg, deleteFoundGenProg, unlinkIfIndexedGenProg_mk,
      readBucketCountGenProg_mk, deleteSwapGenProg_mk, popBackSlotGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readBucketCountProg, clientResult_readBucketCountProg (base, b) s₁ hb, hgm_u1]
  have hcost_base : memoryCost prog s ≤ 16 + memoryCost tail s₁ := by
    simp only [prog, tail, deleteFoundProg, deleteFoundGenProg, unlinkIfIndexedGenProg_mk,
      readBucketCountGenProg_mk, deleteSwapGenProg_mk, popBackSlotGenProg_mk,
      nestedCallPair, deleteFoundMicro, deleteSlotIdx, deleteSlotTarget, deleteFoundLastMicro,
      pure_bind, ← PFunctor.FreeM.bind_eq_bind]
    rw [memoryCost_bind, memoryCost_bind, clientState_readBucketCountProg,
      clientResult_readBucketCountProg (base, b) s₁ hb, hgm_u1]
    dsimp only [s₁, j_last, phys_del, gm₀] at hc_u1 hc_bc ⊢
    exact Nat.le_trans (Nat.add_le_add hc_u1 (Nat.add_le_add_right hc_bc _)) (by omega)
  by_cases hlt : j_del < j_last
  · have hmem_last : j_last < effBucketCap n_max → j_last ∈ L₁ b m_last := fun hcap =>
      (hmem₁ b hb m_last hm_last_lt j_last).mpr
        ⟨(hinv.hchain_mem b hb m_last hm_last_lt j_last).mpr ⟨hj_last_lt, hcap, hm_last_eq.symm⟩,
          fun ⟨_, heq⟩ => by omega⟩
    have hj_not : ∀ m' < numMicroPerBucket n_max, j_del ∉ L₁ b m' := fun m' hm' hin =>
      ((hmem₁ b hb m' hm' j_del).mp hin).2 ⟨rfl, rfl⟩
    let s_mid := (Memory.spec 0).clientState s₁
      (deleteSwapProg U V w₀ n_max h_space ((((base, b), j_del), phys_del), (m_last, j_last)))
    have ⟨hf_sw, hout_sw, hgm_sw, hq_sw, hv_sw, L_mid, hval_mid, hmem_mid⟩ :=
      deleteSwapProg_effect (U := U) (V := V) (w₀ := w₀) (n_max := n_max)
        (h_space := h_space) (base := base) (b := b) (j_del := j_del) (phys_del := phys_del)
        (m_last := m_last) (j_last := j_last) (s := s₁) hw (by rw [hgm_u1]; exact hinv.hslot) hb
        hm_last_lt (by rw [hgm_u1]; exact hbc_pos) hphys_del_lt hj_del_n hj_last_n hval₁ hmem_last
        hj_not
    have hinj := (slotOf_lt_and_injective hinv.hslot).2
    dsimp only [tail] at hst_base hcost_base
    rw [ite_eq_left hlt] at hst_base hcost_base
    have hq_mid : quotAt base U w₀ n_max h_space s_mid.mem =
        Function.update (quotAt base U w₀ n_max h_space s.mem) phys_del
          (quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b j_last)) := by
      rw [hq_sw, hgm_u1, hq_u1]
    have hv_mid : valAt base U V w₀ n_max h_space s_mid.mem =
        Function.update (valAt base U V w₀ n_max h_space s.mem) phys_del
          (valAt base U V w₀ n_max h_space s.mem (slotOf n_max gm₀ b j_last)) := by
      rw [hv_sw, hgm_u1, hv_u1]
    have hc_sw := memoryCost_deleteSwapProg_le U V w₀ n_max h_space
      ((((base, b), j_del), phys_del), (m_last, j_last)) s₁
    refine ⟨s_mid, L_mid, by rw [hst_base, StateTransitionSpec.clientState_bind], by
        rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind] at hcost_base
        dsimp only [s_mid, s₁, phys_del, j_last, gm₀] at hc_sw hcost_base ⊢; omega,
      hf_sw.trans hf_u1, fun a ha => (hout_sw a ha).trans (hout_u1 a (by wram_omega [ha])),
      hgm_sw.trans hgm_u1, fun b' hb' hne j hj => ?_, fun j hj => ?_, hval_mid,
      fun b' hb' hne m' hm' j => by simp [hmem_mid b' hb' m' hm' j, hmem₁ b' hb' m' hm' j, hne],
      fun m' hm' j => ?_⟩
    · have hne_s : slotOf n_max gm₀ b' j ≠ phys_del :=
        fun heq => hne (hinj b' hb' j hj b hb j_del hj_del_lt heq).1
      simp [hq_mid, hv_mid, Function.update_of_ne hne_s]
    · rcases eq_or_ne j j_del with rfl | hjeq
      · simp [idxMap, hq_mid, hv_mid, phys_del]
      · have hne_s : slotOf n_max gm₀ b j ≠ phys_del := fun heq =>
          hjeq (hinj b hb j (hj.trans hj_last_lt) b hb j_del hj_del_lt heq).2
        simp [idxMap, hjeq, hq_mid, hv_mid, Function.update_of_ne hne_s]
    · rw [hmem_mid b hb m' hm' j, hmem₁ b hb m' hm' j, hinv.hchain_mem b hb m' hm' j]
      rcases eq_or_ne j j_del with rfl | hjeq
      · simp only [idxMap, ite_eq_left rfl, true_and, not_true_eq_false, and_false, false_and,
          false_or]
        exact ⟨fun ⟨hm', hcap⟩ => ⟨hlt, hcap, hm' ▸ hm_last_eq.symm⟩,
          fun ⟨_, hcap, hm'⟩ => ⟨hm'.symm.trans hm_last_eq.symm, hcap⟩⟩
      · simp only [idxMap, ite_eq_right hjeq]
        refine ⟨?_, fun ⟨hj_lt, hcap, hm_j⟩ => .inl ⟨⟨⟨hj_lt.trans hj_last_lt, hcap, hm_j⟩,
          fun ⟨_, h⟩ => hjeq h⟩, fun ⟨_, h⟩ => hj_lt.ne h⟩⟩
        rintro (⟨⟨⟨hj_bc, hcap, hm_j⟩, _⟩, hne_last⟩ | ⟨_, _, rfl, _⟩)
        · have : j ≠ j_last := fun h => hne_last ⟨trivial, h⟩
          exact ⟨by dsimp only [j_last, gm₀] at *; omega, hcap, hm_j⟩
        · exact (hjeq rfl).elim
  · dsimp only [tail] at hst_base hcost_base
    rw [ite_eq_right hlt] at hst_base hcost_base
    have hidx (j : ℕ) (hj : j < j_last) : idxMap j = j := ite_eq_right (by omega)
    refine ⟨s₁, L₁, hst_base, by omega, hf_u1,
      fun a ha => hout_u1 a (by wram_omega [ha]), hgm_u1,
      fun _ _ _ _ _ => ⟨by rw [hq_u1], by rw [hv_u1]⟩,
      fun j hj => by rw [hidx j hj, hq_u1, hv_u1]; exact ⟨rfl, rfl⟩,
      hval₁, fun b' hb' hne m' hm' j => by simp [hmem₁ b' hb' m' hm' j, hne],
      fun m' hm' j => ?_⟩
    rw [hmem₁ b hb m' hm' j, hinv.hchain_mem b hb m' hm' j]
    refine ⟨fun ⟨⟨hj_bc, hcap, hm_j⟩, hne⟩ => ?_, fun ⟨hj_lt, hcap, hm_j⟩ =>
      ⟨⟨hj_lt.trans hj_last_lt, hcap, hidx j hj_lt ▸ hm_j⟩, fun ⟨_, heq⟩ => by omega⟩⟩
    have hlt_last : j < j_last := by
      have : j ≠ j_del := fun h => hne ⟨rfl, h⟩
      dsimp only [j_last, gm₀] at *; omega
    exact ⟨hlt_last, hcap, (hidx j hlt_last).symm ▸ hm_j⟩

/-- Transport `BucketStateInv` across removing slot `j_del` (quotient `q_target`) from bucket `b`,
where surviving indices in `b` are mapped by `idxMap j = if j = j_del then j_last else j`. -/
private theorem bucketStateInv_deleteAt
    {U V w₀ n_max h_space base b q_target j_del : ℕ}
    {mOf : ℕ → ℕ} {L L' : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s s' : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max)
    (hj_del_lt : j_del < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)
    (hq_del : quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j_del) = q_target)
    (hslot' : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s'.mem))
    (hchains' : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s'.mem) L')
    (hbc_b' : bCount n_max (gmAt base U V w₀ n_max h_space s'.mem) b =
      bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1)
    (hbc_other' : ∀ b' < numBuckets n_max, b' ≠ b →
      bCount n_max (gmAt base U V w₀ n_max h_space s'.mem) b' =
        bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b')
    (hold_other' : ∀ b' < numBuckets n_max, b' ≠ b →
      ∀ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b',
      quotAt base U w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b' j) =
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j) ∧
      valAt base U V w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b' j) =
      valAt base U V w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j))
    (hold_b' : ∀ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1,
      let idx := if j = j_del then bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1 else j
      quotAt base U w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b j) =
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b idx) ∧
      valAt base U V w₀ n_max h_space s'.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s'.mem) b j) =
      valAt base U V w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b idx))
    (hmem_other' : ∀ b' < numBuckets n_max, b' ≠ b → ∀ m' < numMicroPerBucket n_max, ∀ j,
      j ∈ L' b' m' ↔ j ∈ L b' m')
    (hmem_b' : ∀ m' < numMicroPerBucket n_max, ∀ j,
      j ∈ L' b m' ↔
        j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1 ∧
        j < effBucketCap n_max ∧
        mOf (quotAt base U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b
            (if j = j_del then bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - 1
              else j))) = m') :
    BucketStateInv U V w₀ n_max h_space base mOf L'
      (Function.update B b (Function.update (B b) q_target none)) s' := by
  let gm₀ := gmAt base U V w₀ n_max h_space s.mem
  let j_last := bCount n_max gm₀ b - 1
  let idxMap : ℕ → ℕ := fun j => if j = j_del then j_last else j
  have hidx_lt : ∀ j < j_last, idxMap j < bCount n_max gm₀ b ∧ idxMap j ≠ j_del := fun j hj => by
    dsimp only [idxMap]; split_ifs <;> omega
  have hidx_inj : ∀ j₁ < j_last, ∀ j₂ < j_last, idxMap j₁ = idxMap j₂ → j₁ = j₂ :=
    fun j₁ hj₁ j₂ hj₂ heq => by dsimp only [idxMap] at heq; split_ifs at heq <;> omega
  have hq_ne_target : ∀ j < j_last,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b (idxMap j)) ≠ q_target :=
    fun j hj heq => (hidx_lt j hj).2
      (hinv.hnodup_q b hb _ (hidx_lt j hj).1 j_del hj_del_lt (heq.trans hq_del.symm))
  refine ⟨hslot', hchains',
    fun b' hb' m' hm' j => ?_, fun b' hb' j₁ hj₁ j₂ hj₂ hq_eq => ?_,
    fun b' hb' j hj => ?_, fun b' hb' q => ?_⟩
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [hmem_b' m' hm' j, hbc_b']
      exact and_congr_right fun hj => by simp [(hold_b' j hj).1]
    · rw [hmem_other' b' hb' hbeq m' hm' j, hinv.hchain_mem b' hb' m' hm' j, hbc_other' b' hb' hbeq]
      exact and_congr_right fun hj => by simp [(hold_other' b' hb' hbeq j hj).1]
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [hbc_b'] at hj₁ hj₂
      rw [(hold_b' j₁ hj₁).1, (hold_b' j₂ hj₂).1] at hq_eq
      exact hidx_inj j₁ hj₁ j₂ hj₂
        (hinv.hnodup_q b' hb' _ (hidx_lt j₁ hj₁).1 _ (hidx_lt j₂ hj₂).1 hq_eq)
    · rw [hbc_other' b' hb' hbeq] at hj₁ hj₂
      rw [(hold_other' b' hb' hbeq j₁ hj₁).1, (hold_other' b' hb' hbeq j₂ hj₂).1] at hq_eq
      exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂ hq_eq
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [hbc_b'] at hj
      rw [(hold_b' j hj).1, (hold_b' j hj).2, Function.update_self,
        Function.update_of_ne (hq_ne_target j hj)]
      exact hinv.hmap_some b' hb' _ (hidx_lt j hj).1
    · rw [hbc_other' b' hb' hbeq] at hj
      rw [(hold_other' b' hb' hbeq j hj).1, (hold_other' b' hb' hbeq j hj).2,
        Function.update_of_ne hbeq]
      exact hinv.hmap_some b' hb' j hj
  · rcases eq_or_ne b' b with rfl | hbeq
    · rw [Function.update_self, hbc_b']
      rcases eq_or_ne q q_target with rfl | hqeq
      · simp only [Function.update_self, Option.isSome_none, Bool.false_eq_true, false_iff,
          not_exists, not_and]
        exact fun j hj hq => hq_ne_target j hj ((hold_b' j hj).1 ▸ hq)
      · rw [Function.update_of_ne hqeq, hinv.hmap_dom b' hb' q]
        refine ⟨fun ⟨k, hk, hq_k⟩ => ?_,
          fun ⟨j, hj, hq_j⟩ => ⟨idxMap j, (hidx_lt j hj).1, (hold_b' j hj).1 ▸ hq_j⟩⟩
        have hk_ne : k ≠ j_del := fun heq => hqeq (hq_k.symm.trans (heq ▸ hq_del))
        rcases eq_or_ne k j_last with rfl | hk_last
        · have hdl : j_del < j_last := by dsimp only [j_last, gm₀] at *; omega
          exact ⟨j_del, hdl, by rw [(hold_b' j_del hdl).1, ite_eq_left rfl]; exact hq_k⟩
        · have hkl : k < j_last := by dsimp only [j_last, gm₀] at *; omega
          exact ⟨k, hkl, by rw [(hold_b' k hkl).1, ite_eq_right hk_ne]; exact hq_k⟩
    · rw [Function.update_of_ne hbeq, hbc_other' b' hb' hbeq, hinv.hmap_dom b' hb' q]
      exact exists_congr fun j => and_congr_right fun hj => by
        simp [(hold_other' b' hb' hbeq j hj).1]

/-- Pure state effect, `BucketStateInv` preservation, and amortized `memoryCost` bound of
`deleteFinishProg` following `deletePrepProg` under `BucketStateInv`. -/
theorem deleteFinishProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max)
    (hmOf_lt : ∀ q < 2 ^ quotientBits U n_max, mOf q < numMicroPerBucket n_max) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let prep := (Memory.spec 0).clientResult s
      (deletePrepProg U V w₀ n_max h_space (((base, b), q_target), m))
    let m_last := mOf prep.2
    let d_fin := (((((base, b), deletePrepHdr prep), deletePrepPhys prep), m), m_last)
    let s' := (Memory.spec 0).clientState s (deleteFinishProg U V w₀ n_max h_space d_fin)
    let gm' := gmAt base U V w₀ n_max h_space s'.mem
    let B' := Function.update B b (Function.update (B b) q_target none)
    DeleteFinishPre U V w₀ n_max h_space w d_fin s ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
    (∃ L', BucketStateInv U V w₀ n_max h_space base mOf L' B' s') ∧
    totalSlots n_max gm' =
      (if (B b q_target).isSome then totalSlots n_max gm₀ - 1 else totalSlots n_max gm₀) ∧
    memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 240 := by
  intro gm₀ prep m_last d_fin s' gm' B'
  have ⟨_, _, hq_lt, hprep⟩ :=
    deletePrepProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  dsimp only [deletePrepFound, deletePrepIdx, deletePrepPhys] at hq_lt hprep
  have hm_last_lt : m_last < numMicroPerBucket n_max := hmOf_lt prep.2 hq_lt
  by_cases hex : ∃ j < bCount n_max gm₀ b,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm₀ b j) = q_target
  · rw [ite_eq_left hex] at hprep
    rcases hprep with ⟨hf1, hj_del_lt, hq_del, hphys_del_eq, hq_last_eq⟩
    have hsome : (B b q_target).isSome := (hinv.hmap_dom b hb q_target).mpr hex
    have hm_last_eq : m_last = mOf (quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max gm₀ b (bCount n_max gm₀ b - 1))) := congrArg mOf hq_last_eq
    have hpre_fin : DeleteFinishPre U V w₀ n_max h_space w d_fin s :=
      ⟨henv, fun _ => ⟨henv, hinv.hslot, hb, hm_lt, hm_last_lt, hj_del_lt, by
          dsimp only [d_fin, deletePrepHdr, deletePrepPhys, deleteFinishToFound, deleteFinishPhys,
            deleteSlotPhys]
          exact hphys_del_eq ▸ (slotOf_lt_and_injective hinv.hslot).1 b hb _ hj_del_lt,
        L, hinv.hchains,
        fun hc => (hinv.hchain_mem b hb m hm_lt _).mpr ⟨hj_del_lt, hc, hq_del ▸ hm_eq.symm⟩,
        fun hc => (hinv.hchain_mem b hb m_last hm_last_lt _).mpr
          ⟨by
              dsimp only [d_fin, deletePrepHdr, deletePrepPhys, gm₀, deleteFinishToFound,
                deleteFinishPair, nestedCallBase, nestedCallBucket] at *; omega,
            hc, hm_last_eq.symm⟩⟩⟩
    obtain ⟨s_mid, L_mid, hst_mid, hcost_mid, hf_mid, hout_mid, hgm_mid,
        hold_other_mid, hold_b_mid, hval_mid, hmem_other_mid, hmem_b_mid⟩ :=
      deleteFoundProg_prePop_spec hw hinv hb hm_eq hm_lt hm_last_lt hj_del_lt hq_del hm_last_eq
    have ⟨hf_pop, hout_pop, hlm_pop, hslot', htot', hbc_b', hbc_other', hold_pop, hcost_pop⟩ :=
      popBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max) (h_space := h_space)
        (base := base) (b := b) hw s_mid (hgm_mid.symm ▸ hinv.hslot) hb (by rw [hgm_mid]; omega)
    have hfin : deleteFinishProg U V w₀ n_max h_space d_fin = deleteFoundProg U V w₀ n_max h_space
        ((((base, b), prep.1.1.2), slotOf n_max gm₀ b prep.1.1.2), (m, m_last)) := by
      simp only [d_fin, deletePrepHdr, deletePrepPhys, deleteFinishProg, deleteFinishGenProg,
        deleteFoundGenProg_mk, deleteFinishFound, deleteFinishToFound, deleteFinishPair,
        deleteFinishIdx, deleteFinishPhys, deleteFinishMicro, pure_bind]
      rw [ite_eq_left hf1, hphys_del_eq]
    have hs'_eq : s' = (Memory.spec 0).clientState s_mid
        (popBackSlotProg U V w₀ n_max h_space (base, b)) := by rw [← hst_mid, ← hfin]
    have hcost_fin : memoryCost (deleteFinishProg U V w₀ n_max h_space d_fin) s ≤
        66 + memoryCost (popBackSlotProg U V w₀ n_max h_space (base, b)) s_mid := hfin ▸ hcost_mid
    rw [← hs'_eq] at hf_pop hout_pop hlm_pop hslot' htot' hbc_b' hbc_other' hold_pop hcost_pop
    rw [hgm_mid] at htot' hbc_b' hbc_other' hold_pop hcost_pop
    exact ⟨hpre_fin, hf_pop.trans hf_mid, fun a ha => (hout_pop a ha).trans (hout_mid a ha),
      ⟨L_mid, bucketStateInv_deleteAt hinv hb hj_del_lt hq_del hslot'
        (hval_mid.of_lm_eq hlm_pop) hbc_b' hbc_other'
        (fun b' hb' hne j hj =>
          let hp := hold_pop b' hb' j (by rwa [hbc_other' b' hb' hne])
          let hm := hold_other_mid b' hb' hne j hj
          ⟨hp.1.trans hm.1, hp.2.trans hm.2⟩)
        (fun j hj =>
          let hp := hold_pop b hb j (by rwa [hbc_b'])
          let hm := hold_b_mid j hj
          ⟨hp.1.trans hm.1, hp.2.trans hm.2⟩)
        hmem_other_mid hmem_b_mid⟩,
      by rw [ite_eq_left hsome]; dsimp only [gm₀, gm'] at htot' ⊢; omega,
      by dsimp only [gm₀, gm'] at hcost_pop ⊢; omega⟩
  · rw [ite_eq_right hex] at hprep
    have hnot_some : ¬(B b q_target).isSome := mt (hinv.hmap_dom b hb q_target).mp hex
    have hB_eq : B' = B := by
      simp only [B', Function.update_eq_self_iff, Option.not_isSome_iff_eq_none.mp hnot_some]
    have hne1 : prep.1.1.1 ≠ 1 := by dsimp only [prep]; exact ne_of_eq_of_ne hprep.1 (by decide)
    have hfin : deleteFinishProg U V w₀ n_max h_space d_fin = pure () := by
      simp only [d_fin, deletePrepHdr, deletePrepPhys, deleteFinishProg, deleteFinishGenProg,
        deleteFoundGenProg_mk, deleteFinishFound, pure_bind]
      exact ite_eq_right hne1
    have hs'_eq : s' = s := by dsimp only [s']; rw [hfin]; rfl
    exact ⟨⟨henv, fun h => by
        dsimp only [d_fin, deletePrepHdr, deletePrepPhys, deleteFinishFound] at h; omega⟩,
      by rw [hs'_eq], fun _ _ => by rw [hs'_eq], ⟨L, by rw [hs'_eq, hB_eq]; exact hinv⟩,
      by dsimp only [gm', gm₀]; rw [hs'_eq, ite_eq_right hnot_some],
      by
        dsimp only [gm', gm₀]
        rw [hs'_eq, hfin, memoryCost_pure]; omega⟩

end

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
