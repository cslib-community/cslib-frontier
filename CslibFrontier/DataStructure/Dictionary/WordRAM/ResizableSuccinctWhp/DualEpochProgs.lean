/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochSchedule
-- Unfolds unexposed `Memory.Prog` bodies in the epoch stack for `RealizesBounded` proofs.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `GoodEpochAt` Transport and `Memory.Prog` Control Primitives (`DualEpochProgs`)

This module provides the deterministic `Memory.Prog` building blocks (`RealizesBounded .exact`,
`¬ReadsWidth`) and `GoodEpochAt` preservation lemmas sitting between `LargeEpoch.lean` /
`DualEpochSchedule.lean` and the top-level `RCode .exact` dual-epoch dispatcher
(`DualEpochExec.lean`):

1. **`GoodEpochAt` preservation (`initZeroed`, `transfer_io`, `of_insert`, `of_delete`):**
   Steps `GoodEpochAt fl slack seeds evs mem` across epoch initialization, `SlotIoLayout` mode
   switches (`direct ↔ SplitPair ↔ paged`), `epochInsertProg`, and `epochDeleteProg` via the
   prefix-monotone `WindowCovers` invariant.
2. **Root control header offsets (`hdrU1`–`hdrPBase1`, `[base, base + 192)`):**
   Exact layout of the persistent `192`-word root header, small-epoch 2-word headers
   (`[base + 48, base + 52)`), and dual 64-word `ParamTable` blocks
   (`pBase0 = base + 64`, `pBase1 = base + 128`).
3. **Overflow-free `packedWords` arithmetic (`packedWordsSafe`, `ceil_mul_div_split`):**
   Uses `(n * b + w - 1) / w = (n / w) * b + ((n % w) * b + w - 1) / w` so intermediate products
   never exceed `2 ^ w - 1`, even at `N = U = 2 ^ w - 1` (`11 ≤ w`; realized as
   `packedWordsSafeProg` in `DualEpochTable.lean`).
4. **Control `Memory.Prog` subroutines (`RealizesBounded .exact`, `¬ReadsWidth`):**
   * `setSlotIoProg`: write the 13-word `SlotIoCtx` block (`pBase + 48..60`).
   * `writeSmallParamTableProg`: initialize a small-regime `ParamTable` (`15` writes).
   * `copyParamTableProg`: copy a `64`-word `ParamTable` block between slots `0` and `1` (paired
     with `writeLargeParamTableProg` in `DualEpochTable.lean` for slots `0..47` and `61..62`).
   * `pageInitScalarsBandProg`: write the `14` scalar words of `pagePairInitBand pgB q₀ r_cur`.
   * `migrateBatchProg`: iterate up to `fuel` `epochPopAnyProg → epochInsertProg` steps.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open EpochUpdate

/-! ## Section 1: `GoodEpochAt` Initialization, Transport, and Update Stepping -/

theorem freshCount_append_singleton_insert {U V : ℕ} (evs : List (EpochUpdate U V))
    (u : Fin U) (v : Fin V) :
    freshCount (evs ++ [EpochUpdate.insert u v]) (evs.length + 1) =
      freshCount evs evs.length + (if EpochUpdate.eval evs u = none then 1 else 0) := by
  classical
  have hst := freshCount_succ (evs ++ [EpochUpdate.insert u v]) evs.length
  rw [freshCount_append_left evs [EpochUpdate.insert u v] le_rfl] at hst
  rw [hst]
  congr 1
  unfold isFreshAt
  have hlt : evs.length < (evs ++ [EpochUpdate.insert u v]).length := by simp
  rw [dite_eq_left hlt]
  have hget : (evs ++ [EpochUpdate.insert u v])[evs.length] = EpochUpdate.insert u v := by simp
  have htk : (evs ++ [EpochUpdate.insert u v]).take evs.length = evs := by simp
  rw [hget, htk]
  by_cases hnone : EpochUpdate.eval evs u = none <;> simp [hnone]

theorem freshCount_append_singleton_delete {U V : ℕ} (evs : List (EpochUpdate U V)) (u : Fin U) :
    freshCount (evs ++ [EpochUpdate.delete u]) (evs.length + 1) = freshCount evs evs.length := by
  classical
  have hst := freshCount_succ (evs ++ [EpochUpdate.delete u]) evs.length
  rw [freshCount_append_left evs [EpochUpdate.delete u] le_rfl] at hst
  rw [hst]
  have hf : isFreshAt (evs ++ [EpochUpdate.delete u]) evs.length = false := by
    unfold isFreshAt
    have hlt : evs.length < (evs ++ [EpochUpdate.delete u]).length := by simp
    rw [dite_eq_left hlt]
    have hget : (evs ++ [EpochUpdate.delete u])[evs.length] = EpochUpdate.delete u := by simp
    rw [hget]
  simp [hf]

theorem freshBatch_append_insert_fresh {U V : ℕ} (evs : List (EpochUpdate U V))
    (u : Fin U) (v : Fin V) (Q : ℕ) (hnone : EpochUpdate.eval evs u = none) :
    insert u (freshBatch evs Q (freshCount evs evs.length / Q)) ⊆
      freshBatch (evs ++ [EpochUpdate.insert u v]) Q (freshCount evs evs.length / Q) := by
  classical
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hmem
  · unfold freshBatch
    rw [Finset.mem_image]
    have hlt : evs.length < (evs ++ [EpochUpdate.insert k v]).length := by simp
    refine ⟨⟨evs.length, hlt⟩, ?_, by simp [EpochUpdate.key]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · unfold isFreshAt
      rw [dite_eq_left hlt]
      simp [hnone]
    · rw [freshCount_append_left evs [EpochUpdate.insert k v] le_rfl]
  · exact freshBatch_subset_append evs [EpochUpdate.insert u v] Q _ hmem

private theorem curBufKeysIn_subset {fl : FastEpochLayout}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {S₁ S₂ : Finset (Fin fl.U)}
    (hsub : S₁ ⊆ S₂) (h : CurBufKeysIn (fl := fl) seeds mem S₁) :
    CurBufKeysIn (fl := fl) seeds mem S₂ :=
  fun id b loc u hchk hb hl hk => hsub (h id b loc u hchk hb hl hk)

private theorem cstate_read (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientState s (Memory.read a) = s := rfl

private theorem cres_read (s : Memory.State) (a : ℕ) :
    (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl

private theorem cstate_write (s : Memory.State) (a v : ℕ) :
    (Memory.spec 0).clientState s (Memory.write a v) =
      ⟨Function.update s.mem a v, s.frontier⟩ := rfl

private theorem mcost_read (s : Memory.State) (a : ℕ) :
    memoryCost (Memory.read a) s = 1 := rfl

private theorem mcost_write (s : Memory.State) (a v : ℕ) :
    memoryCost (Memory.write a v) s = 1 := rfl

/-- Initial empty-epoch `GoodEpochAt` after running `epochInitZeroedProg`. -/
theorem GoodEpochAt.initZeroed {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hN : s.mem fl.metaBase = fl.N)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s.mem)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0)
    (hzero_tab : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s.mem addr = 0)
    (hio : fl.io.StateInv 0 slack s.mem) :
    GoodEpochAt fl slack seeds []
      ((Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase)).mem := by
  intro win hgood hcov
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hne0 : fl.N ≠ 0 := hN_pos.ne'
  have hstep : (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase) =
      (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase) := by
    unfold epochInitZeroedProg
    have hp0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
    have hp1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    rw [StateTransitionSpec.clientState_bind, cstate_read, cres_read, hp0,
      StateTransitionSpec.clientState_bind, cstate_read, cres_read, hp1,
      ite_eq_right hne0, StateTransitionSpec.clientState_bind, cstate_write]
    have hst_eq : ({ mem := Function.update s.mem fl.metaBase fl.N, frontier := s.frontier } :
        Memory.State) = s := by
      ext a
      · by_cases ha : a = fl.metaBase
        · subst ha; change Function.update s.mem fl.metaBase fl.N fl.metaBase = s.mem fl.metaBase
          rw [Function.update_self, hN]
        · exact Function.update_of_ne ha fl.N s.mem
      · rfl
    rw [hst_eq]
  rw [hstep]
  have hfr0 : freshCount ([] : List (EpochUpdate fl.U fl.V)) 0 = 0 := freshCount_zero _
  have he_lt : 0 < win.numSubs := by
    have := hcov.sub_lt; simp only [List.length_nil, hfr0, Nat.zero_div] at this; exact this
  obtain ⟨hfg, hcur⟩ := fastInitZeroedProg_good (slack := slack) (⟨0, he_lt⟩ : Fin win.numSubs)
    hgood hv hpt hN hbkt_rep hfp_rep hzero_hdr hzero_tab hio
  have hr₀ : FastLayoutReady w fl s :=
    ⟨hv, hpt, hbkt_rep.1 ▸ seeds.bkt.1.isLt, hfp_rep.1 ▸ seeds.fp.1.isLt⟩
  have hhdr := fastInitZeroedProg_hdr_zero hr₀ hzero_hdr
  have hm2 : ((Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)).mem
      (fl.metaBase + 2) = 0 := hhdr 2 (by decide) (by decide)
  have hss0 : (extractFastMeta fl
      ((Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)).mem).subStep = 0 :=
    hhdr 4 (by decide) (by decide)
  have hfeq : (⟨freshCount ([] : List (EpochUpdate fl.U fl.V)) ([] : List _).length /
      qEpochWhp fl.N, hcov.sub_lt⟩ : Fin win.numSubs) = ⟨0, he_lt⟩ := by
    ext; simp [hfr0]
  refine ⟨hm2, by simp [hss0, hfr0], ?_, curBufKeysIn_subset (Finset.empty_subset _) hcur⟩
  rw [hfeq]
  simpa only [EpochUpdate.eval_nil] using hfg

/-- Transport `GoodEpochAt` across a `SlotIoLayout` change (`io → io₂`) preserving metadata and
`slotIoPairAt` on `[0, nSide)`. -/
theorem GoodEpochAt.transfer_io {fl : FastEpochLayout} {io₂ : SlotIoLayout}
    {w fr slack₁ slack₂ : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {evs : List (EpochUpdate fl.U fl.V)} {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr) (hga : GoodEpochAt fl slack₁ seeds evs m₁)
    (hpt₂ : ({ fl with io := io₂ } : FastEpochLayout).ParamTable m₂)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a)
    (hio₂ : m₁ (fl.metaBase + 2) = 0 →
      io₂.StateInv (extractBlockPool fl.mp m₁).nSide slack₂ m₂)
    (hpair : m₁ (fl.metaBase + 2) = 0 →
      ∀ p < (extractBlockPool fl.mp m₁).nSide,
        slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p) :
    GoodEpochAt { fl with io := io₂ } slack₂ seeds evs m₂ := by
  intro win hgood hcov
  obtain ⟨hm2, hss, hfg, hcur⟩ := hga win hgood hcov
  have hm2' : m₂ (fl.metaBase + 2) = m₁ (fl.metaBase + 2) := hm _ (Or.inl ⟨by omega, by omega⟩)
  have hm4 : m₂ (fl.metaBase + 4) = m₁ (fl.metaBase + 4) := hm _ (Or.inl ⟨by omega, by omega⟩)
  refine ⟨hm2'.trans hm2, hm4.trans hss,
    FastSubEpochGood.transfer_io (fl := fl) (io₂ := io₂) hv hfg hpt₂ hm (hio₂ hm2) (hpair hm2),
    CurBufKeysIn.transfer_io (fl := fl) (io₂ := io₂) hv hfg.inv.bp_inv.1.core hfg.inv.role_lt hm
      (hpair hm2) hcur⟩

/-- Step `GoodEpochAt` across a single `epochInsertProg` (`evs ↦ evs ++ [.insert u v]`). -/
theorem GoodEpochAt.of_insert {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {evs : List (EpochUpdate fl.U fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hga : GoodEpochAt fl 0 seeds evs s.mem) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : EpochUpdate.eval evs u = none →
      s.mem (fl.metaBase + 2) = 0 →
        (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) :
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    GoodEpochAt fl slack' seeds (evs ++ [EpochUpdate.insert u v])
      ((Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u.val), v.val))).mem := by
  classical
  dsimp only
  intro win hgood hcov'
  have hcov : WindowCovers evs win := hcov'.of_append
  obtain ⟨hm2, hss, hfg, hcur⟩ := hga win hgood hcov
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hpt : fl.ParamTable s.mem := hfg.inv.param_table
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u.val), v.val)) =
      (Memory.spec 0).clientState s (fastInsertProg ((fl.pBase, u.val), v.val)) := by
    have hp0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
    have hp1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, cstate_read, cres_read, hp0,
      ite_eq_right hN_pos.ne']
    unfold largeEpochInsertProg
    have hrm_st : (Memory.spec 0).clientState s (fastReadMetaProg (fl.pBase, 2)) = s := rfl
    have hrm_res : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
        s.mem (fl.metaBase + 2) := by
      change s.mem (s.mem (fl.pBase + 1) + 2) = s.mem (fl.metaBase + 2)
      rw [hp1]
    rw [StateTransitionSpec.clientState_bind, hrm_st, hrm_res, hm2, ite_eq_left rfl]
  rw [hstep]
  set Q := qEpochWhp fl.N
  have hQpos : 0 < Q := lt_of_lt_of_le (by decide) (four_le_qEpochWhp fl.N)
  set e : Fin win.numSubs := ⟨freshCount evs evs.length / Q, hcov.sub_lt⟩
  set tNext : Fin win.numSnaps := ⟨evs.length + 1, by simpa using hcov'.len_lt⟩
  have heval_next : EpochUpdate.eval (evs ++ [EpochUpdate.insert u v]) =
      Function.update (EpochUpdate.eval evs) u (some v) := by
    rw [eval_append_singleton]; rfl
  have hsnap : ∀ k : Fin fl.U,
      Function.update (EpochUpdate.eval evs) u (some v) k ≠ none → k ∈ win.snaps tNext := by
    intro k hk
    have hmem : k ∈ liveDom (EpochUpdate.eval
        ((evs ++ [EpochUpdate.insert u v]).take (evs.length + 1))) := by
      have htk : (evs ++ [EpochUpdate.insert u v]).take (evs.length + 1) =
          evs ++ [EpochUpdate.insert u v] := by simp
      rw [htk, heval_next, mem_liveDom_iff]; exact hk
    exact hcov'.snaps_cov tNext (by dsimp only [tNext]; simp) hmem
  have hfr_eq : freshCount (evs ++ [EpochUpdate.insert u v])
      (evs ++ [EpochUpdate.insert u v]).length =
      freshCount evs evs.length + (if EpochUpdate.eval evs u = none then 1 else 0) := by
    simpa only [List.length_append, List.length_singleton] using
      freshCount_append_singleton_insert evs u v
  have hdiv_ge : freshCount evs evs.length / Q ≤
      freshCount (evs ++ [EpochUpdate.insert u v])
        (evs ++ [EpochUpdate.insert u v]).length / Q :=
    Nat.div_le_div_right (by rw [hfr_eq]; omega)
  have hu_in_e : u ∈ win.subUnions e := by
    by_cases hnone : EpochUpdate.eval evs u = none
    · have hsub := hcov'.unions_cov e hdiv_ge
      have hum : u ∈ freshBatch (evs ++ [EpochUpdate.insert u v]) Q e.val :=
        freshBatch_append_insert_fresh evs u v Q hnone (Finset.mem_insert_self u _)
      exact hsub (Finset.mem_union_right _ hum)
    · exact hfg.live_sub u hnone
  obtain ⟨hm2', _, how, hstay, hroll⟩ := fastInsertProg_good hv hfg u v hu_in_e tNext hsnap
    (fun hn => hcap_new hn hm2) hcur
  by_cases hnone : EpochUpdate.eval evs u = none
  · have hfr_s : freshCount (evs ++ [EpochUpdate.insert u v])
        (evs ++ [EpochUpdate.insert u v]).length =
        freshCount evs evs.length + 1 := by rw [hfr_eq, ite_eq_left hnone]
    have hlt_mod : freshCount evs evs.length % Q < Q := Nat.mod_lt _ hQpos
    by_cases hfull : freshCount evs evs.length % Q + 1 < Q
    · obtain ⟨hfg', hss', hcur'⟩ := hstay hnone (by rwa [hss])
      have hdiv_same : (freshCount evs evs.length + 1) / Q = freshCount evs evs.length / Q := by
        have hdm := Nat.div_add_mod (freshCount evs evs.length) Q
        have h1 : freshCount evs evs.length + 1 =
            Q * (freshCount evs evs.length / Q) + (freshCount evs evs.length % Q + 1) := by omega
        rw [h1, Nat.mul_add_div hQpos, Nat.div_eq_of_lt hfull, add_zero]
      have hmod_same : (freshCount evs evs.length + 1) % Q = freshCount evs evs.length % Q + 1 := by
        have hdm := Nat.div_add_mod (freshCount evs evs.length) Q
        have h1 : freshCount evs evs.length + 1 =
            Q * (freshCount evs evs.length / Q) + (freshCount evs evs.length % Q + 1) := by omega
        rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hfull]
      refine ⟨hm2', by rw [hfr_s, hmod_same, hss', hss], ?_, ?_⟩
      · have heq_fin : (⟨freshCount (evs ++ [EpochUpdate.insert u v])
            (evs ++ [EpochUpdate.insert u v]).length / Q,
            hcov'.sub_lt⟩ : Fin win.numSubs) = e :=
          Fin.ext (show freshCount (evs ++ [EpochUpdate.insert u v])
            (evs ++ [EpochUpdate.insert u v]).length / Q = freshCount evs evs.length / Q by
            rw [hfr_s, hdiv_same])
        change FastSubEpochGood 0 0 _ win _ seeds hgood _ _
        rw [heq_fin, heval_next]; exact hfg'
      · refine curBufKeysIn_subset ?_ hcur'
        unfold curBatchAt
        rw [hfr_s, hdiv_same]
        exact freshBatch_append_insert_fresh evs u v Q hnone
    · have hmod_eq : freshCount evs evs.length % Q + 1 = Q := by omega
      obtain ⟨hss', hcur', hnext⟩ := hroll hnone (by rw [hss]; exact hmod_eq)
      have hdiv_next : (freshCount evs evs.length + 1) / Q = freshCount evs evs.length / Q + 1 := by
        have h1 := Nat.div_add_mod (freshCount evs evs.length) Q
        rw [show freshCount evs evs.length + 1 =
          (freshCount evs evs.length / Q + 1) * Q by nlinarith]
        exact Nat.mul_div_cancel _ hQpos
      have hmod_next : (freshCount evs evs.length + 1) % Q = 0 := by
        have h1 := Nat.div_add_mod (freshCount evs evs.length) Q
        rw [show freshCount evs evs.length + 1 =
          (freshCount evs evs.length / Q + 1) * Q by nlinarith]
        exact Nat.mul_mod_left _ _
      set eNext : Fin win.numSubs :=
        ⟨freshCount (evs ++ [EpochUpdate.insert u v])
          (evs ++ [EpochUpdate.insert u v]).length / Q, hcov'.sub_lt⟩
      refine ⟨hm2', by rw [hfr_s, hmod_next, hss'], ?_,
        curBufKeysIn_subset (Finset.empty_subset _) hcur'⟩
      rw [heval_next]
      refine hnext eNext (fun k hk => ?_) ?_
      · have htk : liveDom (EpochUpdate.eval (evs ++ [EpochUpdate.insert u v])) ⊆
            win.subUnions eNext := by
          have hsub := hcov'.unions_cov eNext le_rfl
          have htake := liveDom_take_subset_subStart_union
            (evs ++ [EpochUpdate.insert u v]) hQpos le_rfl
          simp only [List.take_length] at htake
          exact htake.trans hsub
        exact htk (by rw [mem_liveDom_iff, heval_next]; exact hk)
      · have heVal : eNext.val = freshCount evs evs.length / Q + 1 := by
          change freshCount (evs ++ [EpochUpdate.insert u v])
            (evs ++ [EpochUpdate.insert u v]).length / Q = _
          rw [hfr_s, hdiv_next]
        have he0 : 0 < eNext.val := heVal.symm ▸ Nat.succ_pos _
        have hbat := hcov'.batches_cov eNext he0 le_rfl
        have hpred : eNext.val - 1 = freshCount evs evs.length / Q := by
          rw [heVal]; exact Nat.add_sub_cancel _ 1
        rw [hpred] at hbat
        exact (freshBatch_append_insert_fresh evs u v Q hnone).trans hbat
  · have hfr_s : freshCount (evs ++ [EpochUpdate.insert u v])
        (evs ++ [EpochUpdate.insert u v]).length =
        freshCount evs evs.length := by rw [hfr_eq, ite_eq_right hnone, add_zero]
    obtain ⟨hfg', hss', hcur'⟩ := how hnone
    have heq_fin : (⟨freshCount (evs ++ [EpochUpdate.insert u v])
        (evs ++ [EpochUpdate.insert u v]).length / Q,
        hcov'.sub_lt⟩ : Fin win.numSubs) = e :=
      Fin.ext (show freshCount (evs ++ [EpochUpdate.insert u v])
        (evs ++ [EpochUpdate.insert u v]).length / Q = freshCount evs evs.length / Q by
        rw [hfr_s])
    refine ⟨hm2', by rw [hfr_s, hss', hss], by rw [heq_fin, heval_next]; exact hfg',
      curBufKeysIn_subset ?_ hcur'⟩
    unfold curBatchAt; rw [hfr_s]
    exact freshBatch_subset_append evs [EpochUpdate.insert u v] Q _

/-- Step `GoodEpochAt` across a single `epochDeleteProg` (`evs ↦ evs ++ [.delete u]`). -/
theorem GoodEpochAt.of_delete {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {evs : List (EpochUpdate fl.U fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hga : GoodEpochAt fl 0 seeds evs s.mem) (u : Fin fl.U) :
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    GoodEpochAt fl slack' seeds (evs ++ [EpochUpdate.delete u])
      ((Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u.val))).mem := by
  dsimp only
  intro win hgood hcov'
  have hcov : WindowCovers evs win := hcov'.of_append
  obtain ⟨hm2, hss, hfg, hcur⟩ := hga win hgood hcov
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hpt : fl.ParamTable s.mem := hfg.inv.param_table
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u.val)) =
      (Memory.spec 0).clientState s (fastDeleteProg (fl.pBase, u.val)) := by
    have hp0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
    have hp1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, cstate_read, cres_read, hp0,
      ite_eq_right hN_pos.ne']
    unfold largeEpochDeleteProg
    have hrm_st : (Memory.spec 0).clientState s (fastReadMetaProg (fl.pBase, 2)) = s := rfl
    have hrm_res : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
        s.mem (fl.metaBase + 2) := by
      change s.mem (s.mem (fl.pBase + 1) + 2) = s.mem (fl.metaBase + 2)
      rw [hp1]
    rw [StateTransitionSpec.clientState_bind, hrm_st, hrm_res, hm2, ite_eq_left rfl]
  rw [hstep]
  have hspec := fastDeleteProg_spec hv hfg.inv.toInv u
  have hfg' := fastDeleteProg_good hv hfg u
  have hfr_s : freshCount (evs ++ [EpochUpdate.delete u])
      (evs ++ [EpochUpdate.delete u]).length = freshCount evs evs.length := by
    simpa only [List.length_append, List.length_singleton] using
      freshCount_append_singleton_delete evs u
  have heval_next : EpochUpdate.eval (evs ++ [EpochUpdate.delete u]) =
      Function.update (EpochUpdate.eval evs) u none := by
    rw [eval_append_singleton]; rfl
  have heq_fin : (⟨freshCount (evs ++ [EpochUpdate.delete u])
      (evs ++ [EpochUpdate.delete u]).length / qEpochWhp fl.N,
      hcov'.sub_lt⟩ : Fin win.numSubs) =
      ⟨freshCount evs evs.length / qEpochWhp fl.N, hcov.sub_lt⟩ :=
    Fin.ext (show freshCount (evs ++ [EpochUpdate.delete u])
      (evs ++ [EpochUpdate.delete u]).length / qEpochWhp fl.N =
      freshCount evs evs.length / qEpochWhp fl.N by rw [hfr_s])
  refine ⟨hspec.2.2.1.mode_zero, by rw [hfr_s, hspec.2.2.2.2.2.1, hss],
    by rw [heq_fin, heval_next]; exact hfg', curBufKeysIn_subset ?_ (hspec.2.2.2.2.2.2.2.2 _ hcur)⟩
  unfold curBatchAt; rw [hfr_s]
  exact freshBatch_subset_append evs [EpochUpdate.delete u] _ _

/-- Instant extraction of `mode = 0` from `GoodEpochAt` whenever `GoodEpochSeeds` holds on the
canonical `windowOfEvents` for `evs`. -/
theorem GoodEpochAt.mode_zero_of_good {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {evs : List (EpochUpdate fl.U fl.V)}
    {mem : ℕ → ℕ} (hth : whpThreshold fl.c ≤ fl.N)
    (hlen : evs.length ≤ 4 * fl.N)
    (hcard : ∀ k ≤ evs.length, (liveDom (EpochUpdate.eval (evs.take k))).card ≤ fl.N)
    (hga : GoodEpochAt fl slack seeds evs mem)
    (hgood : GoodEpochSeeds (windowOfEvents hth evs hlen hcard) seeds) :
    mem (fl.metaBase + 2) = 0 :=
  (hga (windowOfEvents hth evs hlen hcard) hgood
    (windowCovers_windowOfEvents hth evs hlen hcard)).1

/-! ## Section 2: Root Control Header Offsets (`[base, base + 192)`) -/

/-- Root header offset `0`: `U - 1` (`0 < U < 2 ^ w`). -/
@[expose] def hdrU1 : ℕ := 0
/-- Root header offset `1`: `V - 1` (`0 < V ≤ 2 ^ w`, handles `V = 2 ^ w`). -/
@[expose] def hdrV1 : ℕ := 1
/-- Root header offset `2`: ambient machine word bit-width `w` (`11 ≤ w`). -/
@[expose] def hdrW : ℕ := 2
/-- Root header offset `3`: `keyBits U = Nat.clog 2 U`. -/
@[expose] def hdrKeyBits : ℕ := 3
/-- Root header offset `4`: `valBits V = Nat.clog 2 V`. -/
@[expose] def hdrValBits : ℕ := 4
/-- Root header offset `5`: `if whpThreshold c ≤ U then whpThreshold c else 0`. -/
@[expose] def hdrThresh : ℕ := 5
/-- Root header offset `6`: `if whpThreshold c ≤ U then cTabWhp c else 0`. -/
@[expose] def hdrCTab : ℕ := 6
/-- Root header offset `7`: `if whpThreshold c ≤ U then dTabWhp c else 0`. -/
@[expose] def hdrDTab : ℕ := 7
/-- Root header offset `8`: `redWidthWhp U = max 1 (keyBits U)`. -/
@[expose] def hdrRedW : ℕ := 8
/-- Root header offset `9`: `if whpThreshold c ≤ U then cEff c else 0`. -/
@[expose] def hdrCEff : ℕ := 9
/-- Root header offset `10`: live dictionary size `n_t = #(dom s)`. -/
@[expose] def hdrLive : ℕ := 10
/-- Root header offset `11`: active background rebuild phase tag (`0..11`). -/
@[expose] def hdrPhase : ℕ := 11
/-- Root header offset `12`: active stage (`0 = Stage A`, `1 = Stage B`). -/
@[expose] def hdrStage : ℕ := 12
/-- Root header offset `13`: primary source capacity `N_src` (`0` = small). -/
@[expose] def hdrNSrc : ℕ := 13
/-- Root header offset `14`: destination capacity `N_dst` (`0` = small). -/
@[expose] def hdrNDst : ℕ := 14
/-- Root header offset `15`: in-epoch update counter (`epochOps`, resets on rebuild completion). -/
@[expose] def hdrEpochOps : ℕ := 15
/-- Root header offset `16`: `SplitPairCfg` split cursor `s_split`. -/
@[expose] def hdrSplit : ℕ := 16
/-- Root header offset `17`: batch cursor `cur` inside current sub-phase. -/
@[expose] def hdrCur : ℕ := 17
/-- Root header offset `18`: deterministic remaining ticks in current sub-phase. -/
@[expose] def hdrRem : ℕ := 18
/-- Root header offset `19`: `M_src = epochMetaWordsWhp c w N_src`. -/
@[expose] def hdrMSrc : ℕ := 19
/-- Root header offset `20`: `M_dst = epochMetaWordsWhp c w N_dst`. -/
@[expose] def hdrMDst : ℕ := 20
/-- Root header offset `21`: `pad = max M_src M_dst`. -/
@[expose] def hdrPad : ℕ := 21
/-- Root header offset `22`: `itemBaseLo`. -/
@[expose] def hdrItemLo : ℕ := 22
/-- Root header offset `23`: `itemBaseHi`. -/
@[expose] def hdrItemHi : ℕ := 23
/-- Root header offset `24`: `qLo`. -/
@[expose] def hdrQLo : ℕ := 24
/-- Root header offset `25`: `qHi`. -/
@[expose] def hdrQHi : ℕ := 25
/-- Root header offset `26`: `nSnap` snapshot for `pageInitTailBatchProg`. -/
@[expose] def hdrNSnap : ℕ := 26
/-- Root header offset `27`: `qSnap` snapshot for `pageInitTailBatchProg`. -/
@[expose] def hdrQSnap : ℕ := 27
/-- Root header offset `28`: `unpermDone` flag (`1` after exiting paged mode early). -/
@[expose] def hdrUnpermDone : ℕ := 28
/-- Root header offset `30`: active `log2Calc` accumulator `acc` (word `29` is reserved slack). -/
@[expose] def hdrLogAcc : ℕ := 30
/-- Root header offset `31`: active `log2Calc` exponent counter `k`. -/
@[expose] def hdrLogK : ℕ := 31
/-- Root header offset `32`: computed `Nat.log 2 N_dst`. -/
@[expose] def hdrLogN : ℕ := 32
/-- Root header offset `33`: computed `Dynamic.logLogFactor N_dst`. -/
@[expose] def hdrEll : ℕ := 33
/-- Root header offset `34`: computed `globalPtrBits N_dst = Nat.clog 2 (N_dst + 1)`. -/
@[expose] def hdrPtrB : ℕ := 34
/-- Root header offset `35`: computed `pageSizeWhp N_dst = max 32 (Nat.clog 2 (N_dst + 2))`. -/
@[expose] def hdrPgB : ℕ := 35
/-- Root header offset `36`: `log2Calc` sub-stage (`0..3`). -/
@[expose] def hdrLogSub : ℕ := 36
/-- Root header offset `37`: cached `Nat.clog 2 N_dst` during `log2Calc`. -/
@[expose] def hdrClogN : ℕ := 37
/-- Root header offset `38`: cached `offPageDir c w N_src` when `N_src > 0`. -/
@[expose] def hdrSrcOd : ℕ := 38
/-- Root header offset `39`: cached `offPageTail c w N_src` when `N_src > 0`. -/
@[expose] def hdrSrcOt : ℕ := 39
/-- Root header offset `40`: cached `globalPtrBits N_src` when `N_src > 0`. -/
@[expose] def hdrSrcPb : ℕ := 40
/-- Root header offset `41`: cached `pageSizeWhp N_src` when `N_src > 0`. -/
@[expose] def hdrSrcPg : ℕ := 41
/-- Root header offset `42`: cached `N_src / pageSizeWhp N_src + 4` when `N_src > 0`. -/
@[expose] def hdrSrcMp : ℕ := 42
/-- Root header offset `43`: cached `offPageDir c w N_dst` when `N_dst > 0`. -/
@[expose] def hdrDstOd : ℕ := 43
/-- Root header offset `44`: cached `offPageTail c w N_dst` when `N_dst > 0`. -/
@[expose] def hdrDstOt : ℕ := 44
/-- Root header offset `45`: cached `globalPtrBits N_dst` when `N_dst > 0`. -/
@[expose] def hdrDstPb : ℕ := 45
/-- Root header offset `46`: cached `pageSizeWhp N_dst` when `N_dst > 0`. -/
@[expose] def hdrDstPg : ℕ := 46
/-- Root header offset `47`: cached `N_dst / pageSizeWhp N_dst + 4` when `N_dst > 0`. -/
@[expose] def hdrDstMp : ℕ := 47
/-- Root header offset `48`: small-epoch 2-word header `[0, nSide0]` for slot `0`. -/
@[expose] def hdrSmallMeta0 : ℕ := 48
/-- Root header offset `50`: small-epoch 2-word header `[0, nSide1]` for slot `1`. -/
@[expose] def hdrSmallMeta1 : ℕ := 50
/-- Root header offset `64`: 64-word `ParamTable` block for slot `0` (`[base + 64, base + 128)`). -/
@[expose] def hdrPBase0 : ℕ := 64
/-- Root header offset `128`: 64-word `ParamTable` block for slot `1` (`[base + 128, base + 192)`).
-/
@[expose] def hdrPBase1 : ℕ := 128

/-! ## Section 3: Overflow-Free `packedWords` and `pairStreamWords` Arithmetic -/

/-- Exact division-remainder identity avoiding `(n * k)` overflow: for any `0 < w`,
`(n * k + w - 1) / w = (n / w) * k + ((n % w) * k + w - 1) / w`. -/
theorem ceil_mul_div_split {n k w : ℕ} (hw : 0 < w) :
    (n * k + w - 1) / w = (n / w) * k + ((n % w) * k + w - 1) / w := by
  have hdm : n = n % w + n / w * w := by
    have := Nat.div_add_mod n w; rw [Nat.mul_comm w (n / w)] at this; omega
  have hmul : n * k + w - 1 = (n % w * k + w - 1) + (n / w * k) * w := by
    conv_lhs => rw [hdm]
    have h1 : 1 ≤ w := hw
    have h2 : (n % w + n / w * w) * k = n % w * k + n / w * k * w := by ring
    omega
  rw [hmul, Nat.add_mul_div_right _ _ hw]
  omega

/-- Overflow-free formula for `packedWords n k w`. -/
@[expose] def packedWordsSafe (n k w : ℕ) : ℕ :=
  (n / w) * k + ((n % w) * k + w - 1) / w + 2

theorem packedWordsSafe_eq {n k w : ℕ} (hw : 0 < w) :
    packedWordsSafe n k w = packedWords n k w := by
  unfold packedWordsSafe packedWords
  exact congrArg (· + 2) (ceil_mul_div_split hw).symm

/-- For every `w ≥ 11`, `2 * w ^ 2 + w < 2 ^ w` (`1024 < 2 ^ w` implies `w ≥ 11`). -/
theorem two_mul_sq_add_lt_pow {w : ℕ} (hw : 11 ≤ w) : 2 * w * w + w < 2 ^ w := by
  obtain ⟨d, rfl⟩ : ∃ d, w = d + 11 := ⟨w - 11, by omega⟩
  clear hw
  induction d with
  | zero => decide
  | succ d ih =>
    have hstep : 4 * (d + 11) + 3 ≤ 2 * (d + 11) * (d + 11) + (d + 11) := by nlinarith
    rw [show d + 1 + 11 = (d + 11) + 1 by omega, Nat.pow_succ]
    nlinarith

/-- Whenever `1024 < 2 ^ w`, `11 ≤ w`. -/
theorem le_eleven_of_fits_1024 {w : ℕ} (h : 1024 < 2 ^ w) : 11 ≤ w := by
  by_contra hlt
  have h10 : w ≤ 10 := by omega
  have : 2 ^ w ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) h10
  omega

/-! ## Section 4: Deterministic `Memory.Prog` Control Primitives (`RealizesBounded .exact`) -/

/-- Write the 13-word `SlotIoCtx` block (`pBase + 48..60`, `memoryCost = 13`, `¬ReadsWidth`). -/
def setSlotIoProg : ℕ × SlotIoCtx → Memory.Prog Unit
  | (pBase, ((up, sb), ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)))) => do
    Memory.write (pBase + 48) up
    Memory.write (pBase + 49) sb
    Memory.write (pBase + 50) mb
    Memory.write (pBase + 51) od
    Memory.write (pBase + 52) ot
    Memory.write (pBase + 53) pb
    Memory.write (pBase + 54) wv
    Memory.write (pBase + 55) pg
    Memory.write (pBase + 56) mp
    Memory.write (pBase + 57) ib
    Memory.write (pBase + 58) qb
    Memory.write (pBase + 59) vb
    Memory.write (pBase + 60) nc

@[simp] theorem runClient_frontier_setSlotIoProg (x : ℕ × SlotIoCtx) (s : Memory.State) :
    ((Memory.spec 0).clientState s (setSlotIoProg x)).frontier = s.frontier := by
  rcases x with ⟨pBase, ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
    ⟨⟨qb, vb⟩, nc⟩⟩⟩⟩
  rfl

theorem memoryCost_setSlotIoProg (x : ℕ × SlotIoCtx) (s : Memory.State) :
    memoryCost (setSlotIoProg x) s = 13 := by
  rcases x with ⟨_, ⟨⟨_, _⟩, ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩⟩⟩
  unfold setSlotIoProg
  iterate 12 rw [Realization.memoryCost_bind', mcost_write]
  rw [mcost_write]

theorem setSlotIoProg_frame (pBase : ℕ) (ctx : SlotIoCtx) :
    BoundedFrameProg (fun a => pBase + 48 ≤ a ∧ a < pBase + 61) 13
      (setSlotIoProg (pBase, ctx)) := by
  rcases ctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  unfold setSlotIoProg
  exact
    (BoundedFrameProg.write_prog (by omega) up).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) sb).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) mb).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) od).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) ot).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) pb).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) wv).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) pg).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) mp).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) ib).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) qb).bind_prog fun _ =>
    (BoundedFrameProg.write_prog (by omega) vb).bind_prog fun _ =>
    BoundedFrameProg.write_prog (by omega) nc

theorem setSlotIoProg_mem_vals (pBase : ℕ) (io : SlotIoLayout) (s : Memory.State) :
    let m' := ((Memory.spec 0).clientState s (setSlotIoProg (pBase, io.toCtx))).mem
    m' (pBase + 48) = io.usePaged ∧ m' (pBase + 49) = io.sideBit ∧
    m' (pBase + 50) = io.pgL.metaBase ∧ m' (pBase + 51) = io.pgL.offDir ∧
    m' (pBase + 52) = io.pgL.offTail ∧ m' (pBase + 53) = io.pgL.ptrB ∧
    m' (pBase + 54) = io.pgL.w ∧ m' (pBase + 55) = io.pgL.pgB ∧
    m' (pBase + 56) = io.pgL.maxPages ∧ m' (pBase + 57) = io.pgL.itemBase ∧
    m' (pBase + 58) = io.pgL.qBits ∧ m' (pBase + 59) = io.pgL.vBits ∧
    m' (pBase + 60) = io.pgL.nCap := by
  let s0 := s
  let s1 := (Memory.spec 0).clientState s0 (Memory.write (pBase + 48) io.usePaged)
  let s2 := (Memory.spec 0).clientState s1 (Memory.write (pBase + 49) io.sideBit)
  let s3 := (Memory.spec 0).clientState s2 (Memory.write (pBase + 50) io.pgL.metaBase)
  let s4 := (Memory.spec 0).clientState s3 (Memory.write (pBase + 51) io.pgL.offDir)
  let s5 := (Memory.spec 0).clientState s4 (Memory.write (pBase + 52) io.pgL.offTail)
  let s6 := (Memory.spec 0).clientState s5 (Memory.write (pBase + 53) io.pgL.ptrB)
  let s7 := (Memory.spec 0).clientState s6 (Memory.write (pBase + 54) io.pgL.w)
  let s8 := (Memory.spec 0).clientState s7 (Memory.write (pBase + 55) io.pgL.pgB)
  let s9 := (Memory.spec 0).clientState s8 (Memory.write (pBase + 56) io.pgL.maxPages)
  let s10 := (Memory.spec 0).clientState s9 (Memory.write (pBase + 57) io.pgL.itemBase)
  let s11 := (Memory.spec 0).clientState s10 (Memory.write (pBase + 58) io.pgL.qBits)
  let s12 := (Memory.spec 0).clientState s11 (Memory.write (pBase + 59) io.pgL.vBits)
  let s13 := (Memory.spec 0).clientState s12 (Memory.write (pBase + 60) io.pgL.nCap)
  have heq : (Memory.spec 0).clientState s (setSlotIoProg (pBase, io.toCtx)) = s13 := rfl
  rw [heq]
  have hn : ∀ (a v : ℕ) (st : Memory.State) (j : ℕ), j ≠ a →
      ((Memory.spec 0).clientState st (Memory.write a v)).mem j = st.mem j :=
    fun a v st j h => by rw [cstate_write]; exact Function.update_of_ne h v st.mem
  have hs : ∀ (a v : ℕ) (st : Memory.State),
      ((Memory.spec 0).clientState st (Memory.write a v)).mem a = v :=
    fun a v st => by rw [cstate_write]; exact Function.update_self a v st.mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    iterate 12 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]
    iterate 11 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3]
    iterate 10 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4]
    iterate 9 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5]
    iterate 8 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7, s6]
    iterate 7 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8, s7]
    iterate 6 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9, s8]
    iterate 5 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10, s9]
    iterate 4 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11, s10]
    iterate 3 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12, s11]
    iterate 2 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s13, s12]
    rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · exact hs _ _ _

theorem validHistory_setSlotIoProg {w pBase : ℕ} {io : SlotIoLayout} {s : Memory.State}
    (hfr : pBase + 61 ≤ s.frontier)
    (hf : Fits w io.usePaged ∧ Fits w io.sideBit ∧ Fits w io.pgL.metaBase ∧
      Fits w io.pgL.offDir ∧ Fits w io.pgL.offTail ∧ Fits w io.pgL.ptrB ∧
      Fits w io.pgL.w ∧ Fits w io.pgL.pgB ∧ Fits w io.pgL.maxPages ∧
      Fits w io.pgL.itemBase ∧ Fits w io.pgL.qBits ∧ Fits w io.pgL.vBits ∧
      Fits w io.pgL.nCap) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (setSlotIoProg (pBase, io.toCtx))) := by
  have hw_step : ∀ {a v : ℕ} {st : Memory.State} {rest : Memory.Prog Unit},
      a < st.frontier → Fits w v →
      (Memory.spec w).ValidHistory ⟨Function.update st.mem a v, st.frontier⟩
        ((Memory.spec w).clientHistory ⟨Function.update st.mem a v, st.frontier⟩ rest) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (do Memory.write a v; rest)) := by
    intro a v st rest ha hv hr
    change (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st ((Memory.write a v).bind fun _ => rest))
    rw [validHistory_bind]
    exact ⟨⟨⟨ha, hv⟩, trivial⟩, hr⟩
  unfold setSlotIoProg SlotIoLayout.toCtx PageArenaLayout.toCtx
  have hw_last : ∀ {a v : ℕ} {st : Memory.State}, a < st.frontier → Fits w v →
      (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (Memory.write a v)) :=
    fun ha hv => ⟨⟨ha, hv⟩, trivial⟩
  exact hw_step (by omega) hf.1 <| hw_step (by change pBase + 49 < s.frontier; omega) hf.2.1 <|
    hw_step (by change pBase + 50 < s.frontier; omega) hf.2.2.1 <|
    hw_step (by change pBase + 51 < s.frontier; omega) hf.2.2.2.1 <|
    hw_step (by change pBase + 52 < s.frontier; omega) hf.2.2.2.2.1 <|
    hw_step (by change pBase + 53 < s.frontier; omega) hf.2.2.2.2.2.1 <|
    hw_step (by change pBase + 54 < s.frontier; omega) hf.2.2.2.2.2.2.1 <|
    hw_step (by change pBase + 55 < s.frontier; omega) hf.2.2.2.2.2.2.2.1 <|
    hw_step (by change pBase + 56 < s.frontier; omega) hf.2.2.2.2.2.2.2.2.1 <|
    hw_step (by change pBase + 57 < s.frontier; omega) hf.2.2.2.2.2.2.2.2.2.1 <|
    hw_step (by change pBase + 58 < s.frontier; omega) hf.2.2.2.2.2.2.2.2.2.2.1 <|
    hw_step (by change pBase + 59 < s.frontier; omega) hf.2.2.2.2.2.2.2.2.2.2.2.1 <|
    hw_last (by change pBase + 60 < s.frontier; omega) hf.2.2.2.2.2.2.2.2.2.2.2.2

theorem realizesBounded_setSlotIo :
    RealizesBounded .exact setSlotIoProg
      (WordEncoding.encode (α := ℕ × SlotIoCtx))
      (WordEncoding.encode (α := Unit))
      (fun _ (pBase, _) s => pBase + 61 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨pBase, _⟩
    have hfr_w := hmem.1
    dsimp only [Fits] at *
    omega)

/-- Write `SmallEpochLayout.ParamTable` (`pBase + 0 := 0, pBase + 1 := metaBase`, `setSlotIoProg`).
-/
def writeSmallParamTableProg : (ℕ × ℕ) × SlotIoCtx → Memory.Prog Unit
  | ((pBase, metaBase), ioCtx) => do
    Memory.write pBase 0
    Memory.write (pBase + 1) metaBase
    setSlotIoProg (pBase, ioCtx)

theorem writeSmallParamTableProg_spec (pBase : ℕ) (L : SmallEpochLayout) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (writeSmallParamTableProg ((pBase, L.metaBase), L.io.toCtx))
    s'.frontier = s.frontier ∧
    memoryCost (writeSmallParamTableProg ((pBase, L.metaBase), L.io.toCtx)) s = 15 ∧
    L.ParamTable pBase s'.mem ∧
    (∀ addr, ¬(pBase ≤ addr ∧ addr < pBase + 61) → s'.mem addr = s.mem addr) := by
  unfold writeSmallParamTableProg
  dsimp only
  set s1 := (Memory.spec 0).clientState s (Memory.write pBase 0)
  set s2 := (Memory.spec 0).clientState s1 (Memory.write (pBase + 1) L.metaBase)
  have hfr_eq : (Memory.spec 0).clientState s2 (setSlotIoProg (pBase, L.io.toCtx)) =
      (Memory.spec 0).clientState s
        ((Memory.write pBase 0) >>= fun _ => (Memory.write (pBase + 1) L.metaBase) >>= fun _ =>
          setSlotIoProg (pBase, L.io.toCtx)) := by
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  have hfr2 : s2.frontier = s.frontier := rfl
  have hvals := setSlotIoProg_mem_vals pBase L.io s2
  have hframe := setSlotIoProg_frame pBase L.io.toCtx
  have hm0 : ((Memory.spec 0).clientState s2 (setSlotIoProg (pBase, L.io.toCtx))).mem pBase =
      0 := by
    rw [hframe.mem_outside s2 pBase (by omega)]
    change Function.update (Function.update s.mem pBase 0) (pBase + 1) L.metaBase pBase = 0
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm1 : ((Memory.spec 0).clientState s2 (setSlotIoProg (pBase, L.io.toCtx))).mem (pBase + 1) =
      L.metaBase := by
    rw [hframe.mem_outside s2 (pBase + 1) (by omega)]
    change Function.update (Function.update s.mem pBase 0) (pBase + 1) L.metaBase (pBase + 1) =
      L.metaBase
    rw [Function.update_self]
  refine ⟨by rw [← hfr_eq, hframe.frontier_eq, hfr2], ?_, ?_, fun addr ha => ?_⟩
  · rw [Realization.memoryCost_bind', mcost_write,
      Realization.memoryCost_bind', mcost_write, memoryCost_setSlotIoProg]
  · rw [← hfr_eq]
    exact ⟨hm0, hm1, hvals.1, hvals.2.1, hvals.2.2.1, hvals.2.2.2.1, hvals.2.2.2.2.1,
      hvals.2.2.2.2.2.1, hvals.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2.1,
      hvals.2.2.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2.2.2.2.1,
      hvals.2.2.2.2.2.2.2.2.2.2.2.1, hvals.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [← hfr_eq, hframe.mem_outside s2 addr (by omega)]
    change Function.update (Function.update s.mem pBase 0) (pBase + 1) L.metaBase addr = s.mem addr
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem validHistory_writeSmallParamTableProg {w pBase : ℕ} {L : SmallEpochLayout}
    {s : Memory.State} (hfr : pBase + 61 ≤ s.frontier)
    (hmb : Fits w L.metaBase)
    (hf : Fits w L.io.usePaged ∧ Fits w L.io.sideBit ∧ Fits w L.io.pgL.metaBase ∧
      Fits w L.io.pgL.offDir ∧ Fits w L.io.pgL.offTail ∧ Fits w L.io.pgL.ptrB ∧
      Fits w L.io.pgL.w ∧ Fits w L.io.pgL.pgB ∧ Fits w L.io.pgL.maxPages ∧
      Fits w L.io.pgL.itemBase ∧ Fits w L.io.pgL.qBits ∧ Fits w L.io.pgL.vBits ∧
      Fits w L.io.pgL.nCap) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (writeSmallParamTableProg ((pBase, L.metaBase), L.io.toCtx))) := by
  unfold writeSmallParamTableProg
  change (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s
      ((Memory.write pBase 0).bind fun _ =>
        (Memory.write (pBase + 1) L.metaBase).bind fun _ =>
          setSlotIoProg (pBase, L.io.toCtx)))
  rw [validHistory_bind]
  refine ⟨⟨⟨by omega, by dsimp only [Fits]; positivity⟩, trivial⟩, ?_⟩
  rw [validHistory_bind]
  refine ⟨⟨⟨by change pBase + 1 < s.frontier; omega, hmb⟩, trivial⟩, ?_⟩
  exact validHistory_setSlotIoProg (by change pBase + 61 ≤ s.frontier; exact hfr) hf

theorem realizesBounded_writeSmallParamTable :
    RealizesBounded .exact writeSmallParamTableProg
      (WordEncoding.encode (α := (ℕ × ℕ) × SlotIoCtx))
      (WordEncoding.encode (α := Unit))
      (fun _ ((pBase, _), _) s => pBase + 61 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hsio := realizesBounded_setSlotIo
  realize
  all_goals (
    rcases d with ⟨⟨pBase, _⟩, _⟩
    have hfr_w := hmem.1
    dsimp only [Fits] at *
    omega)

/-- Single-word copy step `dst + k ← src + k` (`2` memory accesses, `1 ≤ memoryCost`). -/
def copyWordStepProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((src, dst), k) => do
    let v ← Memory.read (src + k)
    Memory.write (dst + k) v
    pure (k + 1)

theorem memoryCost_copyWordStepProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (copyWordStepProg x) s = 2 := by
  rcases x with ⟨⟨src, dst⟩, k⟩
  unfold copyWordStepProg
  rw [Realization.memoryCost_bind', mcost_read,
    Realization.memoryCost_bind', mcost_write, memoryCost_pure]

theorem realizesBounded_copyWordStep :
    RealizesBounded .exact copyWordStepProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ ((src, dst), k) s =>
        src + k < s.frontier ∧ dst + k < s.frontier ∧ k + 1 < 65 ∧ src + 64 ≤ s.frontier ∧
          dst + 64 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨src, dst⟩, k⟩
    have hfr_w := hmem.1
    dsimp only [Fits] at *
    omega)

/-- Copy `64` contiguous words `[src, src + 64)` into `[dst, dst + 64)` (`128` memory ops). -/
def copyParamTableProg : ℕ × ℕ → Memory.Prog Unit
  | (src, dst) => do
    let _ ← iterate copyWordStepProg (src, dst) 64 0
    pure ()

theorem copyParamTableProg_spec {src dst : ℕ} (hdisj : dst + 64 ≤ src ∨ src + 64 ≤ dst)
    (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (copyParamTableProg (src, dst))
    s'.frontier = s.frontier ∧
    memoryCost (copyParamTableProg (src, dst)) s = 128 ∧
    (∀ k < 64, s'.mem (dst + k) = s.mem (src + k)) ∧
    (∀ addr, ¬(dst ≤ addr ∧ addr < dst + 64) → s'.mem addr = s.mem addr) := by
  have hiter : ∀ (n k : ℕ) (st : Memory.State), k + n ≤ 64 →
      let st' := (Memory.spec 0).clientState st (iterate copyWordStepProg (src, dst) n k)
      st'.frontier = st.frontier ∧
      (Memory.spec 0).clientResult st (iterate copyWordStepProg (src, dst) n k) = k + n ∧
      memoryCost (iterate copyWordStepProg (src, dst) n k) st = 2 * n ∧
      (∀ j, j < n → st'.mem (dst + k + j) = st.mem (src + k + j)) ∧
      (∀ addr, ¬(dst + k ≤ addr ∧ addr < dst + k + n) → st'.mem addr = st.mem addr) := by
    intro n
    induction n with
    | zero =>
      intro k st _
      exact ⟨rfl, rfl, memoryCost_pure _ _, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ => rfl⟩
    | succ m ih =>
      intro k st hkn
      dsimp only
      have hstep_res : (Memory.spec 0).clientResult st (copyWordStepProg ((src, dst), k)) =
          k + 1 := rfl
      set st1 := (Memory.spec 0).clientState st (copyWordStepProg ((src, dst), k))
      have hm1 : st1.mem = Function.update st.mem (dst + k) (st.mem (src + k)) := rfl
      have hfr1 : st1.frontier = st.frontier := rfl
      have hc1 : memoryCost (copyWordStepProg ((src, dst), k)) st = 2 :=
        memoryCost_copyWordStepProg _ _
      obtain ⟨hfr', hres', hc', hcp', hout'⟩ := ih (k + 1) st1 (by omega)
      have hit_eq : iterate copyWordStepProg (src, dst) (m + 1) k =
          (copyWordStepProg ((src, dst), k) >>=
            fun k' => iterate copyWordStepProg (src, dst) m k') := rfl
      refine ⟨?_, ?_, ?_, fun j hj => ?_, fun addr ha => ?_⟩
      · rw [hit_eq, StateTransitionSpec.clientState_bind, hstep_res]; exact hfr'.trans hfr1
      · rw [hit_eq, StateTransitionSpec.clientResult_bind, hstep_res]; rw [hres']; omega
      · rw [hit_eq, Realization.memoryCost_bind', hstep_res, hc1, hc']; omega
      · rw [hit_eq, StateTransitionSpec.clientState_bind, hstep_res]
        by_cases hj0 : j = 0
        · subst hj0
          simp only [add_zero]
          exact (hout' (dst + k) (by omega)).trans (by rw [hm1, Function.update_self])
        · have hj1 := hcp' (j - 1) (by omega)
          have hdst_eq : dst + k + j = dst + (k + 1) + (j - 1) := by omega
          have hsrc_eq : src + k + j = src + (k + 1) + (j - 1) := by omega
          rw [hdst_eq]
          exact hj1.trans (by
            rw [hm1, Function.update_of_ne (by rcases hdisj with h | h <;> omega), ← hsrc_eq])
      · rw [hit_eq, StateTransitionSpec.clientState_bind, hstep_res]
        exact (hout' addr (by omega)).trans (by rw [hm1, Function.update_of_ne (by omega)])
  obtain ⟨hfr, _, hc, hcp, hout⟩ := hiter 64 0 s (by decide)
  unfold copyParamTableProg
  have hcb : (Memory.spec 0).clientState s
      (iterate copyWordStepProg (src, dst) 64 0 >>= fun _ => pure ()) =
      (Memory.spec 0).clientState s (iterate copyWordStepProg (src, dst) 64 0) := by
    rw [StateTransitionSpec.clientState_bind]; rfl
  refine ⟨by rw [hcb]; exact hfr,
    by rw [Realization.memoryCost_bind', memoryCost_pure, add_zero]; exact hc,
    fun k hk => by rw [hcb]; simpa only [add_zero] using hcp k hk,
    fun addr ha => by rw [hcb]; exact hout addr (by simpa only [add_zero] using ha)⟩

theorem validHistory_copyParamTableProg {w src dst : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hs : src + 64 ≤ s.frontier) (hd : dst + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (copyParamTableProg (src, dst))) := by
  have hiter : ∀ (n k : ℕ) (st : Memory.State), k + n ≤ 64 →
      Memory.WellFormed w st → src + 64 ≤ st.frontier → dst + 64 ≤ st.frontier →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate copyWordStepProg (src, dst) n k)) := by
    intro n
    induction n with
    | zero => intro _ _ _ _ _ _; exact trivial
    | succ m ih =>
      intro k st hkn hwf_st hs_st hd_st
      change (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st
          ((copyWordStepProg ((src, dst), k)).bind fun k' =>
            iterate copyWordStepProg (src, dst) m k'))
      rw [validHistory_bind, clientResult_width, clientState_width]
      have hfit : Fits w (st.mem (src + k)) := hwf_st.mem_fits (src + k)
      have hstep : (Memory.spec w).ValidHistory st
          ((Memory.spec w).clientHistory st (copyWordStepProg ((src, dst), k))) := by
        unfold copyWordStepProg
        change (Memory.spec w).ValidHistory st
          ((Memory.spec w).clientHistory st ((Memory.read (src + k)).bind fun v =>
            (Memory.write (dst + k) v).bind fun _ => pure (k + 1)))
        rw [validHistory_bind, clientResult_width, clientState_width]
        refine ⟨⟨show src + k < st.frontier by omega, trivial⟩, ?_⟩
        rw [validHistory_bind]
        exact ⟨⟨⟨by change dst + k < st.frontier; omega, hfit⟩, trivial⟩, trivial⟩
      refine ⟨hstep, ih (k + 1) _ (by omega) ?_ hs_st hd_st⟩
      rw [← clientState_width w, ← (Memory.spec w).run_runClient _ st]
      exact hwf_st.run hstep
  change (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s
      ((iterate copyWordStepProg (src, dst) 64 0).bind fun _ => pure ()))
  rw [validHistory_bind]
  exact ⟨hiter 64 0 s (by decide) hwf hs hd, trivial⟩

theorem realizesBounded_copyParamTable :
    RealizesBounded .exact copyParamTableProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (src, dst) s => 7 ≤ w ∧ src + 64 ≤ s.frontier ∧ dst + 64 ≤ s.frontier)
      (fun _ _ => 0) := by
  have hcw := realizesBounded_copyWordStep
  have hpos : ∀ a s, 1 ≤ memoryCost (copyWordStepProg a) s := fun a s => by
    rw [memoryCost_copyWordStepProg]; omega
  have hbatch : RealizesBounded .exact
      (fun x : ((ℕ × ℕ) × ℕ) × ℕ => iterate copyWordStepProg x.1.1 x.2 x.1.2)
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((src, dst), cur), fuel) s =>
        iterationSafe copyWordStepProg
          (fun _ ((src, dst), k) st =>
            src + k < st.frontier ∧ dst + k < st.frontier ∧ k + 1 < 65 ∧
              src + 64 ≤ st.frontier ∧ dst + 64 ≤ st.frontier)
          w (src, dst) fuel cur s)
      (fun _ _ => 0) :=
    RealizesBounded.iterate₀
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      hcw hpos
  have hsafe : ∀ {w src dst n k : ℕ} {st : Memory.State},
      k + n ≤ 64 → src + 64 ≤ st.frontier → dst + 64 ≤ st.frontier →
      iterationSafe copyWordStepProg
        (fun _ ((src, dst), j) s0 =>
          src + j < s0.frontier ∧ dst + j < s0.frontier ∧ j + 1 < 65 ∧
            src + 64 ≤ s0.frontier ∧ dst + 64 ≤ s0.frontier)
        w (src, dst) n k st := by
    intro w src dst n
    induction n with
    | zero => intro _ _ _ _ _; exact trivial
    | succ m ih =>
      intro k st hkn hs hd
      refine ⟨⟨by omega, by omega, by omega, hs, hd⟩, ?_⟩
      change iterationSafe copyWordStepProg _ w (src, dst) m (k + 1) _
      exact ih (by omega) hs hd
  have hcb : copyParamTableProg = fun p : ℕ × ℕ =>
      (iterate copyWordStepProg p 64 0).bind fun _ => pure () := by
    funext ⟨src, dst⟩; rfl
  clear hcb
  realize
  all_goals (
    rcases d with ⟨src, dst⟩
    first
      | exact hsafe (by decide) h.2.1 h.2.2
      | (have hw7 : 7 ≤ w := h.1
         have hpow7 : 128 ≤ 2 ^ w :=
           (by decide : 128 = 2 ^ 7) ▸ Nat.pow_le_pow_right (by decide) hw7
         have hfr_w := hmem.1
         dsimp only [Fits] at *
         omega))

/-- Initialize `[mb + 18, mb + 32)` to the exact `14` scalar words of `pagePairInitBand pgB q₀
r_cur` (`memoryCost = 14`, `¬ReadsWidth`). -/
def pageInitScalarsBandProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((mb, pgB), (q₀, r_cur)) => do
    Memory.write (mb + 18) 0
    Memory.write (mb + 19) 0
    Memory.write (mb + 20) pgB
    Memory.write (mb + 21) q₀
    Memory.write (mb + 22) 0
    Memory.write (mb + 23) r_cur
    Memory.write (mb + 24) 0
    Memory.write (mb + 25) 0
    Memory.write (mb + 26) 0
    Memory.write (mb + 27) 0
    Memory.write (mb + 28) 0
    Memory.write (mb + 29) 0
    Memory.write (mb + 30) 0
    Memory.write (mb + 31) 0

theorem pageInitScalarsBandProg_spec (mb pgB q₀ r_cur : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (pageInitScalarsBandProg ((mb, pgB), (q₀, r_cur)))
    s'.frontier = s.frontier ∧
    memoryCost (pageInitScalarsBandProg ((mb, pgB), (q₀, r_cur))) s = 14 ∧
    s'.mem (mb + 18) = 0 ∧ s'.mem (mb + 19) = 0 ∧ s'.mem (mb + 20) = pgB ∧
    s'.mem (mb + 21) = q₀ ∧ s'.mem (mb + 22) = 0 ∧ s'.mem (mb + 23) = r_cur ∧
    s'.mem (mb + 24) = 0 ∧ s'.mem (mb + 25) = 0 ∧ s'.mem (mb + 26) = 0 ∧
    s'.mem (mb + 27) = 0 ∧ s'.mem (mb + 28) = 0 ∧ s'.mem (mb + 29) = 0 ∧
    s'.mem (mb + 30) = 0 ∧ s'.mem (mb + 31) = 0 ∧
    (∀ addr, ¬(mb + 18 ≤ addr ∧ addr < mb + 32) → s'.mem addr = s.mem addr) := by
  dsimp only
  have hmc : memoryCost (pageInitScalarsBandProg ((mb, pgB), (q₀, r_cur))) s = 14 := by
    unfold pageInitScalarsBandProg
    iterate 13 rw [Realization.memoryCost_bind', mcost_write]
    rw [mcost_write]
  have hn : ∀ (a v : ℕ) (st : Memory.State) (j : ℕ), j ≠ a →
      ((Memory.spec 0).clientState st (Memory.write a v)).mem j = st.mem j :=
    fun a v st j h => by rw [cstate_write]; exact Function.update_of_ne h v st.mem
  have hs : ∀ (a v : ℕ) (st : Memory.State),
      ((Memory.spec 0).clientState st (Memory.write a v)).mem a = v :=
    fun a v st => by rw [cstate_write]; exact Function.update_self a v st.mem
  let s1 := (Memory.spec 0).clientState s (Memory.write (mb + 18) 0)
  let s2 := (Memory.spec 0).clientState s1 (Memory.write (mb + 19) 0)
  let s3 := (Memory.spec 0).clientState s2 (Memory.write (mb + 20) pgB)
  let s4 := (Memory.spec 0).clientState s3 (Memory.write (mb + 21) q₀)
  let s5 := (Memory.spec 0).clientState s4 (Memory.write (mb + 22) 0)
  let s6 := (Memory.spec 0).clientState s5 (Memory.write (mb + 23) r_cur)
  let s7 := (Memory.spec 0).clientState s6 (Memory.write (mb + 24) 0)
  let s8 := (Memory.spec 0).clientState s7 (Memory.write (mb + 25) 0)
  let s9 := (Memory.spec 0).clientState s8 (Memory.write (mb + 26) 0)
  let s10 := (Memory.spec 0).clientState s9 (Memory.write (mb + 27) 0)
  let s11 := (Memory.spec 0).clientState s10 (Memory.write (mb + 28) 0)
  let s12 := (Memory.spec 0).clientState s11 (Memory.write (mb + 29) 0)
  let s13 := (Memory.spec 0).clientState s12 (Memory.write (mb + 30) 0)
  let s14 := (Memory.spec 0).clientState s13 (Memory.write (mb + 31) 0)
  have heq : (Memory.spec 0).clientState s (pageInitScalarsBandProg ((mb, pgB), (q₀, r_cur))) =
      s14 := rfl
  rw [heq]
  refine ⟨rfl, hmc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun addr ha => ?_⟩
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    iterate 13 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]
    iterate 12 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3]
    iterate 11 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4]
    iterate 10 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5]
    iterate 9 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6]
    iterate 8 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7]
    iterate 7 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8]
    iterate 6 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9]
    iterate 5 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10]
    iterate 4 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12, s11]
    iterate 3 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13, s12]
    iterate 2 rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · dsimp only [s14, s13]
    rw [hn _ _ _ _ (by omega)]
    exact hs _ _ _
  · exact hs _ _ _
  · dsimp only [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
    iterate 14 rw [hn _ _ _ _ (by omega)]

theorem validHistory_pageInitScalarsBandProg {w mb pgB q₀ r_cur : ℕ} {s : Memory.State}
    (hfr : mb + 32 ≤ s.frontier)
    (hpgB : Fits w pgB) (hq₀ : Fits w q₀) (hr : Fits w r_cur) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (pageInitScalarsBandProg ((mb, pgB), (q₀, r_cur)))) := by
  have hz : Fits w 0 := by dsimp only [Fits]; positivity
  have hw_step : ∀ {a v : ℕ} {st : Memory.State} {rest : Memory.Prog Unit},
      a < st.frontier → Fits w v →
      (Memory.spec w).ValidHistory ⟨Function.update st.mem a v, st.frontier⟩
        ((Memory.spec w).clientHistory ⟨Function.update st.mem a v, st.frontier⟩ rest) →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (do Memory.write a v; rest)) := by
    intro a v st rest ha hv hr'
    change (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st ((Memory.write a v).bind fun _ => rest))
    rw [validHistory_bind]
    exact ⟨⟨⟨ha, hv⟩, trivial⟩, hr'⟩
  have hw_last : ∀ {a v : ℕ} {st : Memory.State}, a < st.frontier → Fits w v →
      (Memory.spec w).ValidHistory st ((Memory.spec w).clientHistory st (Memory.write a v)) :=
    fun ha hv => ⟨⟨ha, hv⟩, trivial⟩
  unfold pageInitScalarsBandProg
  exact hw_step (by omega) hz <| hw_step (by change mb + 19 < s.frontier; omega) hz <|
    hw_step (by change mb + 20 < s.frontier; omega) hpgB <|
    hw_step (by change mb + 21 < s.frontier; omega) hq₀ <|
    hw_step (by change mb + 22 < s.frontier; omega) hz <|
    hw_step (by change mb + 23 < s.frontier; omega) hr <|
    hw_step (by change mb + 24 < s.frontier; omega) hz <|
    hw_step (by change mb + 25 < s.frontier; omega) hz <|
    hw_step (by change mb + 26 < s.frontier; omega) hz <|
    hw_step (by change mb + 27 < s.frontier; omega) hz <|
    hw_step (by change mb + 28 < s.frontier; omega) hz <|
    hw_step (by change mb + 29 < s.frontier; omega) hz <|
    hw_step (by change mb + 30 < s.frontier; omega) hz <|
    hw_last (by change mb + 31 < s.frontier; omega) hz

theorem realizesBounded_pageInitScalarsBand :
    RealizesBounded .exact pageInitScalarsBandProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun _ ((mb, _), _) s => mb + 32 ≤ s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨mb, _⟩, _⟩
    have hfr_w := hmem.1
    dsimp only [Fits] at *
    omega)

/-- Single migration step: pops one `(u, v)` from `pSrc` if `0 < nSide(pSrc)` and inserts it into
`pDst` (`epochReadNSideProg`, `epochPopAnyProg`, `epochInsertProg`). Returns `0` so the iteration
accumulator never overflows `2 ^ w` even at `w = 11` (`itemBatchWhp = 2048 = 2 ^ 11`). -/
def migrateStepProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((pSrc, pDst), _moved) => do
    let nS ← epochReadNSideProg pSrc
    if 0 < nS then do
      let qv ← epochPopAnyProg pSrc
      epochInsertProg ((pDst, qv.1), qv.2)
      pure 0
    else
      pure 0

/-- Precondition for a single `migrateStepProg` iteration. -/
@[expose] def MigrateStepPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((pSrc, pDst), _), s =>
    EpochProgPre w pSrc s ∧
    (0 < (Memory.spec 0).clientResult s (epochReadNSideProg pSrc) →
      EpochInsertProgPre w pDst ((Memory.spec 0).clientState s (epochPopAnyProg pSrc)))

theorem memoryCost_migrateStepProg_pos (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (migrateStepProg x) s := by
  rcases x with ⟨⟨pSrc, pDst⟩, moved⟩
  unfold migrateStepProg
  rw [Realization.memoryCost_bind']
  have h1 : 1 ≤ memoryCost (epochReadNSideProg pSrc) s := by
    unfold epochReadNSideProg
    rw [Realization.memoryCost_bind', mcost_read]
    omega
  omega

theorem realizesBounded_migrateStep :
    RealizesBounded .exact migrateStepProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      MigrateStepPre (fun _ _ => 0) := by
  have hrn := realizesBounded_epochReadNSide
  have hpa := realizesBounded_epochPopAny
  have hin := realizesBounded_epochInsert
  realize
  all_goals (
    rcases d with ⟨⟨pSrc, pDst⟩, moved⟩
    obtain ⟨hsrc, hdst⟩ := h
    first | exact hsrc | exact hdst ‹_›)

/-- Batched migration step draining up to `fuel` items from `pSrc` into `pDst`. -/
def migrateBatchProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((pSrc, pDst), moved), fuel) => iterate migrateStepProg (pSrc, pDst) fuel moved

theorem realizesBounded_migrateBatch :
    RealizesBounded .exact migrateBatchProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((pSrc, pDst), moved), fuel) s =>
        iterationSafe migrateStepProg MigrateStepPre w (pSrc, pDst) fuel moved s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_migrateStep
    memoryCost_migrateStepProg_pos

/-- Single-step `Nat.clog 2` / `Nat.log 2` doubling helper: given `(target, (acc, k))`, if
`acc < target` return `((acc * 2), k + 1)` else `(acc, k)` (pure word-bounded computation when
`target ≤ 2 ^ (w - 1)` — handled via shift-right `rem ← rem / 2` to avoid `acc * 2` overflowing
`2 ^ w` when `N_dst > 2 ^ (w - 1)`!). -/
def logHalfStep (rem k : ℕ) : ℕ × ℕ :=
  if 1 < rem then (rem / 2, k + 1) else (rem, k)

theorem logHalfStep_iter_eq (n : ℕ) (hn : 0 < n) (t : ℕ) (ht : Nat.log 2 n ≤ t) :
    ((Nat.iterate (fun p : ℕ × ℕ => logHalfStep p.1 p.2) t (n, 0)).1 = 1 ∧
     (Nat.iterate (fun p : ℕ × ℕ => logHalfStep p.1 p.2) t (n, 0)).2 = Nat.log 2 n) := by
  suffices h : ∀ (r t k : ℕ), 0 < r → Nat.log 2 r ≤ t →
      (Nat.iterate (fun p : ℕ × ℕ => logHalfStep p.1 p.2) t (r, k)).1 = 1 ∧
      (Nat.iterate (fun p : ℕ × ℕ => logHalfStep p.1 p.2) t (r, k)).2 = k + Nat.log 2 r by
    simpa only [zero_add] using h n t 0 hn ht
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro t k hr hlt
    cases t with
    | zero =>
      have hr1 : r = 1 := by
        have h0 : Nat.log 2 r = 0 := by omega
        by_contra hne
        have : 2 ≤ r := by omega
        have : 1 ≤ Nat.log 2 r := by
          rw [Nat.le_log_iff_pow_le Nat.one_lt_two hr.ne']; omega
        omega
      subst hr1; simp
    | succ m =>
      rw [Function.iterate_succ_apply]
      by_cases h1 : 1 < r
      · have hstep : logHalfStep r k = (r / 2, k + 1) := by
          unfold logHalfStep; exact ite_eq_left h1
        change ((fun p : ℕ × ℕ => logHalfStep p.1 p.2)^[m] (logHalfStep r k)).1 = 1 ∧
          ((fun p : ℕ × ℕ => logHalfStep p.1 p.2)^[m] (logHalfStep r k)).2 = k + Nat.log 2 r
        rw [hstep]
        have hdiv_lt : r / 2 < r := Nat.div_lt_self hr (by decide)
        have hdiv_pos : 0 < r / 2 := by omega
        have hlog_eq : Nat.log 2 r = Nat.log 2 (r / 2) + 1 :=
          Nat.log_of_one_lt_of_le (by decide) h1
        have hih := ih (r / 2) hdiv_lt m (k + 1) hdiv_pos (by omega)
        exact ⟨hih.1, by rw [hih.2, hlog_eq]; omega⟩
      · have hr1 : r = 1 := by omega
        subst hr1
        have hstep : logHalfStep 1 k = (1, k) := by
          unfold logHalfStep; exact ite_eq_right (by omega)
        change ((fun p : ℕ × ℕ => logHalfStep p.1 p.2)^[m] (logHalfStep 1 k)).1 = 1 ∧
          ((fun p : ℕ × ℕ => logHalfStep p.1 p.2)^[m] (logHalfStep 1 k)).2 = k + Nat.log 2 1
        rw [hstep]
        have h1m : ∀ j : ℕ,
            Nat.iterate (fun p : ℕ × ℕ => logHalfStep p.1 p.2) j (1, k) = (1, k) := by
          intro j; induction j with
          | zero => rfl
          | succ j ihj =>
            rw [Function.iterate_succ_apply, show logHalfStep 1 k = (1, k) from hstep]; exact ihj
        rw [h1m m]; simp

/-- Compute `Nat.clog 2 n` directly from `Nat.log 2 (n - 1) + 1` (for `n ≥ 2`). -/
theorem clog_eq_log_pred_succ {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  have h1 : n - 1 ≠ 0 := by omega
  have hlo : 2 ^ Nat.log 2 (n - 1) ≤ n - 1 := Nat.pow_log_le_self 2 h1
  have hhi : n - 1 < 2 ^ (Nat.log 2 (n - 1) + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two (n - 1)
  have hle : Nat.clog 2 n ≤ Nat.log 2 (n - 1) + 1 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (by omega)
  have hge : Nat.log 2 (n - 1) < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
