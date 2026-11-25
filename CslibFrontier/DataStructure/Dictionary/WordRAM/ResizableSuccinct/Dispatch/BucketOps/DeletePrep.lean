/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `fcBucket` and unfolds `compFeistelCoordsProg` in `DeletePrep` obligations.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Deletion Phase 1: Bucket Search and Last-Quotient Read (`Memory.Prog`)

Implements `compDeletePrepWithHashGenProg` along with its `RealizesBounded .exact` and
`ValidProg` certificates, and internal helpers used by the dictionary-level deletion proof.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeletePrepWithHashGenProg`:
  Feistel-dispatched Phase 1 of compacted deletion.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 4: Compacted Two-Phase Deletion (`compDeletePrepWithHashGenProg`,
`compDeleteFinishWithHashGenProg`) -/

private def compDeletePrepFoundProg :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | (((cp, (metaBase, itemBase)), b), res) => do
    let phys_last ← compLastSlotOfGenProg ((cp, metaBase), b)
    let q_last ← compReadPhysQuotGenProg ((cp, (metaBase, itemBase)), phys_last)
    pure (res, q_last)

private def CompDeletePrepFoundPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), b), _res), s =>
    ∃ U V N m_items s_fix,
      cp = mkCompParams U V w N ∧
      CompEpochEnv U V w N metaBase itemBase m_items s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items ∧
      b < numBuckets N ∧
      1 ≤ bCount N (compGmAt metaBase U w N s.mem) b

private theorem realizesBounded_compDeletePrepFound :
    RealizesBounded .exact compDeletePrepFoundProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompDeletePrepFoundPre (fun _ _ => 0) := by
  have hls := realizesBounded_compLastSlotOfGen
  have hrq := realizesBounded_compReadPhysQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, b⟩, res⟩
    obtain ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb, hbc⟩ := h)
  · exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb, hbc⟩
  · rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
    exact ⟨U, V, N, m_items, s_fix, b, bCount N (compGmAt metaBase U w N s.mem) b - 1,
      rfl, henv, hcpl, hslot, hm_items, hb, Nat.sub_lt hbc Nat.one_pos, rfl⟩

/-- Compacted Phase 1 of `delete` at bucket level (`¬ReadsWidth`):
searches bucket `(b, m)` for `q_target`, and if `found = 1`, reads `q_last` of the last slot in
bucket `b`; otherwise returns `(((0, 0), 0), 0)`. -/
private def compDeletePrepBodyGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | (((cp, (metaBase, itemBase)), (b, q_target)), m) => do
    let res ← compSearchBucketGenProg ((((cp, (metaBase, itemBase)), (b, q_target)), m))
    let z1 ← pure 1
    if sbFound res = z1 then
      compDeletePrepFoundProg (((cp, (metaBase, itemBase)), b), res)
    else do
      let z0 ← pure 0
      pure (((z0, z0), z0), z0)

private theorem compDeletePrepBodyGenProg_spec
    {metaBase itemBase U V w N m_items b q_target m : ℕ} {L : List ℕ} {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_items : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let prog := compDeletePrepBodyGenProg
      ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))
    let prog_fix := deletePrepProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
      (((0, b), q_target), m)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s_fix prog_fix ∧
    memoryCost prog s ≤ 20 + 12 * L.length + 10 * (bCount N gm b - effBucketCap N) := by
  intro gm prog prog_fix
  obtain ⟨hst_sb, hres_sb, hcost_sb⟩ := compSearchBucketGenProg_spec
    (q_target := q_target) henv hcpl hslot hm_items hb hm hchain hc_lt
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm hchain hc_lt
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have hchain_fix : IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b) L := by
    change IsDLChain N
      (lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b m)
      (lmPrev N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b)
      (lmNext N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b) L
    rw [← hcpl.lm_eq]; exact hchain
  have hc_lt_fix : ∀ j ∈ L,
      j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b := by
    change ∀ j ∈ L,
      j < bCount N (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b
    rw [← hcpl.gm_eq]; exact hc_lt
  have hst_sb_fix :
      (Memory.spec 0).clientState s_fix
        (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
          (((0, b), q_target), m)) = s_fix :=
    (searchBucketProg_spec
      (d := (((0, b), q_target), m))
      (ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V)
      hb hm hslot_fix hchain_fix hc_lt_fix).1
  rcases hres_eq : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres_eq] at hres_sb hfnd
  have hfix_eq : (Memory.spec 0).clientResult s_fix prog_fix =
      (Memory.spec 0).clientResult s_fix
        (if found = 1 then do
          let phys_last ← lastSlotOfProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (0, b)
          let q_last ← readQuotProg U (ghostW w) N (epochHashSpace U (ghostW w) N) (0, phys_last)
          pure (((found, j_found), phys_found), q_last)
        else pure (((0, 0), 0), 0)) := by
    dsimp only [prog_fix, deletePrepProg, deletePrepGenProg]
    simp only [searchBucketGenProg_mk, lastSlotOfGenProg_mk, readQuotGenProg_mk, pure_bind]
    rw [StateTransitionSpec.clientResult_bind, hst_sb_fix, ← hres_sb]
  rw [hfix_eq]
  dsimp only [prog, compDeletePrepBodyGenProg, gm]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, hst_sb, hres_eq,
    StateTransitionSpec.clientResult_bind, hst_sb, hres_eq,
    memoryCost_bind_of_clientState_eq hst_sb _, hres_eq]
  dsimp only [sbFound]
  split_ifs with hf1
  · obtain ⟨hj_bc, _⟩ := hfnd hf1
    have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hj_last : bCount N (compGmAt metaBase U w N s.mem) b - 1 <
        bCount N (compGmAt metaBase U w N s.mem) b := by omega
    have hbc_fix : 1 ≤ bCount N
        (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) b := by
      rw [← hcpl.gm_eq]; exact hbc
    have hphys_last_lt : slotOf N (compGmAt metaBase U w N s.mem) b
        (bCount N (compGmAt metaBase U w N s.mem) b - 1) < N :=
      (slotOf_lt_and_injective hslot).1 b hb _ hj_last
    dsimp only [compDeletePrepFoundProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compLastSlotOfGenProg,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      StateTransitionSpec.clientState_bind, clientState_compReadPhysQuotGenProg,
      StateTransitionSpec.clientState_pure,
      StateTransitionSpec.clientResult_bind, clientState_compLastSlotOfGenProg,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      StateTransitionSpec.clientResult_bind, clientState_compReadPhysQuotGenProg,
      clientResult_compReadPhysQuot_slotOf hcpl henv hslot hm_items hb hj_last,
      StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_bind, clientState_lastSlotOfProg,
      clientResult_lastSlotOfProg (0, b) s_fix hslot_fix hb hbc_fix]
    simp only [← hcpl.gm_eq]
    rw [StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
      clientResult_readQuotProg s_fix hphys_last_lt,
      StateTransitionSpec.clientResult_pure,
      memoryCost_bind_of_clientState_eq (clientState_compLastSlotOfGenProg _ s) _,
      clientResult_compLastSlotOfGenProg hslot hb hbc,
      memoryCost_bind_of_clientState_eq (clientState_compReadPhysQuotGenProg _ s) _,
      memoryCost_pure]
    have hc1 := memoryCost_compLastSlotOfGenProg_le ((mkCompParams U V w N, metaBase), b) s
    have hc2 := memoryCost_compReadPhysQuotGenProg_le
      ((mkCompParams U V w N, (metaBase, itemBase)),
        slotOf N (compGmAt metaBase U w N s.mem) b
          (bCount N (compGmAt metaBase U w N s.mem) b - 1)) s
    exact ⟨trivial, rfl, by omega⟩
  · rw [StateTransitionSpec.clientState_pure, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientResult_pure, memoryCost_pure]
    exact ⟨rfl, rfl, by omega⟩

private theorem realizesBounded_compDeletePrepBodyGen :
    RealizesBounded .exact compDeletePrepBodyGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompSearchBucketPre (fun _ _ => 0) := by
  have hsb := realizesBounded_compSearchBucketGen
  have hfd := realizesBounded_compDeletePrepFound
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
    obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
      hb, hm_lt, hchain, hc_lt⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1)
  · exact ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩
  · exact fits_const_of_offCompItems hfit_meta (by decide)
  · have hst_b := (compSearchBucketGenProg_spec (q_target := q_target)
      henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
    have hfnd := searchBucket_found_slotOf (q_target := q_target)
      henv hcpl hslot hm_items hb hm_lt hchain hc_lt
    change CompDeletePrepFoundPre w _
      ((Memory.spec 0).clientState s
        (compSearchBucketGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))))
    rw [hst_b]
    dsimp only at hc
    rcases hres : (Memory.spec 0).clientResult s
        (compSearchBucketGenProg
          ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
      ⟨⟨found, j_found⟩, phys_found⟩
    rw [hres] at hfnd hc
    dsimp only [sbFound] at hc
    obtain ⟨hj_bc, _⟩ := hfnd hc
    exact ⟨U, V, N, m_items, s_fix, rfl, henv, hcpl, hslot, hm_items, hb,
      Nat.one_le_of_lt hj_bc⟩

private theorem validProg_compDeletePrepBodyGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ} {s : Memory.State}
    (h : CompSearchBucketPre w d s) : ValidProg w 0 s (compDeletePrepBodyGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, q_target⟩⟩, m⟩
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := h
  have hst_sb := (compSearchBucketGenProg_spec (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  have hfnd := searchBucket_found_slotOf (q_target := q_target)
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt
  dsimp only [compDeletePrepBodyGenProg, compDeletePrepFoundProg]
  simp only [pure_bind]
  refine validProg_bind (validProg_compSearchBucketGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rw [hst_sb]
  rcases hres : (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), (b, q_target)), m))) with
    ⟨⟨found, j_found⟩, phys_found⟩
  rw [hres] at hfnd
  dsimp only [sbFound]
  refine validProg_ite (fun hc => ?_) (fun _ => validProg_pure _)
  obtain ⟨hj_bc, _⟩ := hfnd hc
  have hbc : 1 ≤ bCount N (compGmAt metaBase U w N s.mem) b := by omega
  refine validProg_bind
    (validProg_compLastSlotOfGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb, hbc⟩) ?_
  rw [clientState_compLastSlotOfGenProg, clientResult_compLastSlotOfGenProg hslot hb hbc]
  refine validProg_bind
    (validProg_compReadPhysQuotGen
      ⟨U, V, N, m_items, s_fix, b, bCount N (compGmAt metaBase U w N s.mem) b - 1,
        rfl, henv, hcpl, hslot, hm_items, hb, by omega, rfl⟩) ?_
  exact validProg_pure _

/-- Feistel-dispatched Phase 1 of compacted `delete` (`¬ReadsWidth`):
`d = ((cp, (metaBase, itemBase)), (u, h_q))`, returning `(((found, j_del), phys_del), q_last)`. -/
def compDeletePrepWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ)
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    compDeletePrepBodyGenProg (((cp, (metaBase, itemBase)), c.1), c.2)

theorem realizesBounded_compDeletePrepWithHashGen :
    RealizesBounded .exact compDeletePrepWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hdp := realizesBounded_compDeletePrepBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compDeletePrepWithHashGen {w : ℕ}
    {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compDeletePrepWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨_, hsb_pre⟩ := h
  dsimp only [compDeletePrepWithHashGenProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  exact validProg_compDeletePrepBodyGen hsb_pre


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
