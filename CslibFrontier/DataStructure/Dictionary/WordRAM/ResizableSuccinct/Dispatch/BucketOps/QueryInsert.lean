/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `fcBucket` and `gmAt_prependIfIndexedProg`, and unfolds `compFeistelCoordsProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Compacted Feistel-Dispatched Lookup and Split Insertion (`Memory.Prog`)

Implements `compQueryWithHashGenProg`, `compInsertSearchWithHashGenProg`,
`compWritePhysValGenProg`, and `compInsertAppendNewGenProg` along with their
`RealizesBounded .exact` and `ValidProg` certificates.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compQueryWithHashGenProg`:
  Feistel-dispatched compacted lookup.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertSearchWithHashGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compWritePhysValGenProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compInsertAppendNewGenProg`:
  split two-phase compacted insertion subroutines.
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

/-- Resolve physical slot `phys` through `denseOfPhysGenProg` and overwrite its value with `v_new`
(`¬ReadsWidth`). -/
def compWritePhysValGenProg : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), phys), v_new) => do
    let d_idx ← denseOfPhysGenProg ((cp, metaBase), phys)
    writeCompValGenProg (((cp, itemBase), d_idx), v_new)

private theorem memoryCost_compWritePhysValGenProg_le
    (d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compWritePhysValGenProg d) s ≤ 8 := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
  dsimp only [compWritePhysValGenProg]
  simp only [Realization.memoryCost_bind', runClient_state_denseOfPhysGenProg,
    memoryCost_writeCompValGenProg]
  have h1 := memoryCost_denseOfPhysGenProg_le ((cp, metaBase), phys) s
  omega

/-- Precondition for `compWritePhysValGenProg`. -/
@[expose] def CompWritePhysValPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), phys), _v_new), s =>
    CompReadPhysItemPre w ((cp, (metaBase, itemBase)), phys) s

private theorem compWritePhysValGenProg_effect {metaBase itemBase U V w N m_cap b j v_new : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm_cap : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_cap)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hv_lt : v_new < 2 ^ valBits V) :
    let phys := slotOf N (compGmAt metaBase U w N s.mem) b j
    let s' := (Memory.spec 0).clientState s
      (compWritePhysValGenProg (((mkCompParams U V w N, (metaBase, itemBase)), phys), v_new))
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, phys), v_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro phys s' s_fix'
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_cap hb hj
  have hd_cap : denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem)
      phys < m_cap := lt_of_lt_of_le hd_lt hm_cap
  have hs'_eq : s' = ⟨writeCompVal itemBase U V w N s.mem
      (denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) phys) v_new,
      s.frontier⟩ := by
    dsimp only [s', compWritePhysValGenProg, phys]
    rw [StateTransitionSpec.clientState_bind, clientState_denseOfPhysGenProg,
      clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj,
      clientState_writeCompValGenProg]
  rw [hs'_eq]
  exact ⟨⟨rfl, fun a _ hi => writeCompVal_outside henv.pos_w hd_cap s.mem hi⟩,
    hcpl.writeVal_slotOf henv.pos_w henv.meta_le_item hslot hb hj hv_lt⟩

theorem realizesBounded_compWritePhysValGen :
    RealizesBounded .exact compWritePhysValGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      CompWritePhysValPre (fun _ _ => 0) := by
  have hdp := realizesBounded_denseOfPhysGen
  have hwv := realizesBounded_writeCompValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
    obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items,
      hb, hj, rfl⟩ := h)
  · exact hcpl.denseOfPhysPre_slotOf henv hslot hb hj
  · rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
    obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
    exact ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩

theorem validProg_compWritePhysValGen {w : ℕ} {d : ((CompParams × (ℕ × ℕ)) × ℕ) × ℕ}
    {s : Memory.State} (h : CompWritePhysValPre w d s) :
    ValidProg w 0 s (compWritePhysValGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, phys⟩, v_new⟩
  obtain ⟨U, V, N, m_items, s_fix, b, j, rfl, henv, hcpl, hslot, hm_items, hb, hj, rfl⟩ := h
  dsimp only [compWritePhysValGenProg]
  refine validProg_bind (validProg_denseOfPhysGen (hcpl.denseOfPhysPre_slotOf henv hslot hb hj)) ?_
  rw [clientState_denseOfPhysGenProg, clientResult_denseOfPhys_slotOf hcpl henv hslot hb hj]
  obtain ⟨hd_lt, _, _⟩ := hcpl.quot_val_at_slotOf hslot hm_items hb hj
  exact validProg_writeCompValGen ⟨m_items, henv.compItemEnv, lt_of_lt_of_le hd_lt hm_items⟩


/-- Feistel-dispatched compacted dictionary lookup (`¬ReadsWidth`):
`d = ((cp, (metaBase, itemBase)), (u, h_q))`, returning `Option ℕ`. -/
def compQueryWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (Option ℕ)
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    compQueryBodyGenProg (((cp, (metaBase, itemBase)), c.1), c.2)


theorem realizesBounded_compQueryWithHashGen :
    RealizesBounded .exact compQueryWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Option ℕ))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hqb := realizesBounded_compQueryBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compQueryWithHashGen {w : ℕ} {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)}
    {s : Memory.State} (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compQueryWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨hfc_pre, hsb_pre⟩ := h
  dsimp only [compQueryWithHashGenProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  exact validProg_compQueryBodyGen hsb_pre

private def compPackInsertSearchResProg :
    ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | (((found, _j), phys), ((b, _q), m)) => pure ((found, phys), (b, m))

private theorem clientState_compPackInsertSearchResProg
    (x : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (compPackInsertSearchResProg x) = s := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

private theorem clientResult_compPackInsertSearchResProg
    (res : (ℕ × ℕ) × ℕ) (b q m : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (compPackInsertSearchResProg (res, ((b, q), m))) =
      ((res.1.1, res.2), (b, m)) := by
  rcases res with ⟨⟨_, _⟩, _⟩; rfl

private theorem memoryCost_compPackInsertSearchResProg
    (x : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (compPackInsertSearchResProg x) s = 0 := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩; rfl

private theorem realizesBounded_compPackInsertSearchRes :
    RealizesBounded .exact compPackInsertSearchResProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Phase 1 of split compacted insertion (`¬ReadsWidth`):
computes Feistel coordinates `(b, q, m)` from `(u, h_q)`, searches bucket `(b, m)` for `q`, and
returns `((found, phys), (b, m))`. -/
def compInsertSearchWithHashGenProg :
    (CompParams × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((cp, (metaBase, itemBase)), (u, h_q)) => do
    let c ← compFeistelCoordsProg (cp, (u, h_q))
    let res ← compSearchBucketGenProg (((cp, (metaBase, itemBase)), c.1), c.2)
    compPackInsertSearchResProg (res, c)

theorem realizesBounded_compInsertSearchWithHashGen :
    RealizesBounded .exact compInsertSearchWithHashGenProg
      (WordEncoding.encode (α := (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      CompQueryWithHashPre (fun _ _ => 0) := by
  have hfc := realizesBounded_compFeistelCoords
  have hsb := realizesBounded_compSearchBucketGen
  have hpk := realizesBounded_compPackInsertSearchRes
  realize
  all_goals (
    rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
    obtain ⟨hfc_pre, hsb_pre⟩ := h)
  · exact hfc_pre
  · rw [clientState_compFeistelCoordsProg]
    exact hsb_pre

theorem validProg_compInsertSearchWithHashGen {w : ℕ}
    {d : (CompParams × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompQueryWithHashPre w d s) :
    ValidProg w 0 s (compInsertSearchWithHashGenProg d) := by
  rcases d with ⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨u, h_q⟩⟩
  obtain ⟨_, hsb_pre⟩ := h
  obtain ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items,
    hb, hm_lt, hchain, hc_lt⟩ := hsb_pre
  have hst := (compSearchBucketGenProg_spec (q_target := u >>> cpBucketBits (mkCompParams U V w N))
    henv hcpl hslot hm_items hb hm_lt hchain hc_lt).1
  dsimp only [compInsertSearchWithHashGenProg, compPackInsertSearchResProg]
  refine validProg_bind (validProg_compFeistelCoords _ s) ?_
  rw [clientState_compFeistelCoordsProg]
  refine validProg_bind (validProg_compSearchBucketGen
    ⟨U, V, N, m_items, s_fix, L, rfl, henv, hcpl, hslot, hm_items, hb, hm_lt, hchain, hc_lt⟩) ?_
  rcases (Memory.spec 0).clientResult s
      (compSearchBucketGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)),
          ((h_q &&& cpBucketMask (mkCompParams U V w N)) ^^^
            (u &&& cpBucketMask (mkCompParams U V w N)),
            u >>> cpBucketBits (mkCompParams U V w N))),
          h_q >>> cpBucketBits (mkCompParams U V w N)))) with ⟨⟨found, j⟩, phys⟩
  rcases (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u, h_q))) with ⟨⟨b0, q0⟩, m0⟩
  exact validProg_pure _

/-- Phase 2b (miss path) of split compacted insertion (`¬ReadsWidth`):
after `growZeroCode` has extended `s.frontier` to cover `n + 1` dense items, appends `(q, v)` to
bucket `b` (`q = u >>> cpBucketBits cp`) and prepends the new slot to micro-chain `(b, m)` if
indexed. -/
def compInsertAppendNewGenProg :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, (metaBase, itemBase)), (b, m)), (u, v)) => do
    let q ← compExtractQuotGenProg (cp, u)
    let j_new ← readCompBucketCountGenProg ((cp, metaBase), b)
    compPushBackSlotGenProg ((((cp, (metaBase, itemBase)), b), q), v)
    compPrependIfIndexedGenProg (((cp, metaBase), (b, m)), j_new)

/-- Precondition for `compInsertAppendNewGenProg`. -/
@[expose] def CompInsertAppendNewPre (w : ℕ) :
    ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, (metaBase, itemBase)), (b, m)), (u, v)), s =>
    ∃ U V N m_cap s_fix,
      cp = mkCompParams U V w N ∧
      Fits w u ∧
      u >>> bucketBits N < 2 ^ quotientBits U N ∧
      v < 2 ^ valBits V ∧
      CompEpochEnv U V w N metaBase itemBase m_cap s ∧
      FixedCoupled metaBase itemBase U V w N s_fix s ∧
      SlotStoreInv N (compGmAt metaBase U w N s.mem) ∧
      b < numBuckets N ∧
      m < numMicroPerBucket N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) < N ∧
      totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap ∧
      lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N


private theorem compLmAt_pushBackSlot_eq {metaBase itemBase U V w N m_cap b q v : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : q < 2 ^ quotientBits U N) (hv_lt : v < 2 ^ valBits V) :
    compLmAt metaBase U w N ((Memory.spec 0).clientState s
      (compPushBackSlotGenProg ((((mkCompParams U V w N, (metaBase, itemBase)), b), q), v))).mem =
      compLmAt metaBase U w N s.mem := by
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  obtain ⟨-, hcpl_pb, -⟩ :=
    compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt hv_lt
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have htot_fix : totalSlots N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rw [← hcpl.gm_eq]; exact htot
  have eff_pb_fix := pushBackSlotProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (q_val := q) (v_val := v)
    hwg s_fix hslot_fix hb htot_fix hq_lt hv_lt
  exact hcpl_pb.lm_eq.trans (eff_pb_fix.2.2.1.trans hcpl.lm_eq.symm)

private theorem compInsertAppendNewGenProg_effect {metaBase itemBase U V w N m_cap b m u v : ℕ}
    {s_fix s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_cap s)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hm : m < numMicroPerBucket N)
    (htot : totalSlots N (compGmAt metaBase U w N s.mem) < N)
    (hm_cap : totalSlots N (compGmAt metaBase U w N s.mem) + 1 ≤ m_cap)
    (hq_lt : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N)
    (hv_lt : v < 2 ^ valBits V)
    (hold : lmHead N (compLmAt metaBase U w N s.mem) b m ≤ effBucketCap N) :
    let q := keyQuotient (bucketBits N) u
    let j_new := bCount N (compGmAt metaBase U w N s.mem) b
    let d := ((((mkCompParams U V w N, (metaBase, itemBase)), (b, m)), (u, v)))
    let s' := (Memory.spec 0).clientState s (compInsertAppendNewGenProg d)
    let s_fix' := (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s_fix
        (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v)))
      (prependIfIndexedProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), m), j_new))
    CompOpFrame metaBase itemBase U V w N m_cap s s' ∧
    FixedCoupled metaBase itemBase U V w N s_fix' s' ∧
    memoryCost (compInsertAppendNewGenProg d) s +
      98 * slotPotential N (compGmAt metaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt metaBase U w N s.mem) + 200 := by
  intro q j_new d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  obtain ⟨hfr_pb, hcpl_pb, hcost_pb⟩ :=
    compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt hv_lt
  set s₁ := (Memory.spec 0).clientState s
    (compPushBackSlotGenProg ((((mkCompParams U V w N, (metaBase, itemBase)), b), q), v))
  set s_fix₁ := (Memory.spec 0).clientState s_fix
    (pushBackSlotProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) (((0, b), q), v))
  have hslot_fix : SlotStoreInv N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) := by
    rw [← hcpl.gm_eq]; exact hslot
  have htot_fix : totalSlots N
      (gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem) < N := by
    rw [← hcpl.gm_eq]; exact htot
  have eff_pb_fix := pushBackSlotProg_effect (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (q_val := q) (v_val := v)
    hwg s_fix hslot_fix hb htot_fix hq_lt hv_lt
  have hlm_s₁ : compLmAt metaBase U w N s₁.mem = compLmAt metaBase U w N s.mem :=
    hcpl_pb.lm_eq.trans (eff_pb_fix.2.2.1.trans hcpl.lm_eq.symm)
  have hold₁ : lmHead N (compLmAt metaBase U w N s₁.mem) b m ≤ effBucketCap N := by
    rw [hlm_s₁]; exact hold
  have hold_fix₁ :
      lmHead N (lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix₁.mem) b m ≤
        effBucketCap N := by
    rw [← hcpl_pb.lm_eq]; exact hold₁
  obtain ⟨hfr_pr, hcpl_pr⟩ := compPrependIfIndexedGenProg_effect
    (m_cap := m_cap) (j_new := j_new) henv.pos_w henv.meta_le_item hcpl_pb hb hm hold₁
  have hgm_pr_fix := gmAt_prependIfIndexedProg (U := U) (V := V) (w := ghostW w) (n_max := N)
    (h_space := epochHashSpace U (ghostW w) N) (base := 0) (b := b) (m := m) (j_new := j_new)
    hwg hb hm s_fix₁ hold_fix₁
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (compPrependIfIndexedGenProg (((mkCompParams U V w N, metaBase), (b, m)), j_new)) := by
    dsimp only [s', d, compInsertAppendNewGenProg, s₁, q, j_new]
    rw [StateTransitionSpec.clientState_bind, clientState_compExtractQuotGenProg,
      clientResult_compExtractQuotGenProg, StateTransitionSpec.clientState_bind,
      clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb,
      StateTransitionSpec.clientState_bind]
  have hgm'_eq : compGmAt metaBase U w N s'.mem = compGmAt metaBase U w N s₁.mem := by
    rw [hs'_eq]
    exact hcpl_pr.gm_eq.trans (hgm_pr_fix.trans hcpl_pb.gm_eq.symm)
  have hcost_tot : memoryCost (compInsertAppendNewGenProg d) s ≤
      22 + memoryCost (compPushBackSlotGenProg
        ((((mkCompParams U V w N, (metaBase, itemBase)), b), q), v)) s := by
    dsimp only [d, compInsertAppendNewGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compExtractQuotGenProg _ s) _,
      memoryCost_compExtractQuotGenProg, clientResult_compExtractQuotGenProg,
      memoryCost_bind_of_clientState_eq (clientState_readCompBucketCountGenProg _ s) _,
      clientResult_readCompBucketCountGenProg hb, Realization.memoryCost_bind']
    have hc1 := memoryCost_readCompBucketCountGenProg_le ((mkCompParams U V w N, metaBase), b) s
    have hc2 := memoryCost_compPrependIfIndexedGenProg_le
      (((mkCompParams U V w N, metaBase), (b, m)), j_new) s₁
    dsimp only [s₁, q, j_new] at hc2 ⊢
    omega
  rw [hgm'_eq]
  exact ⟨by rw [hs'_eq]; exact hfr_pb.trans hfr_pr,
    by rw [hs'_eq]; exact hcpl_pr,
    by dsimp only [s₁, q] at hcost_pb hcost_tot ⊢; omega⟩

theorem realizesBounded_compInsertAppendNewGen :
    RealizesBounded .exact compInsertAppendNewGenProg
      (WordEncoding.encode (α := ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      CompInsertAppendNewPre (fun _ _ => 0) := by
  have heq := realizesBounded_compExtractQuotGen
  have hbc := realizesBounded_readCompBucketCountGen
  have hpb := realizesBounded_compPushBackSlotGen
  have hpr := realizesBounded_compPrependIfIndexedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, m⟩⟩, ⟨u, v⟩⟩
    obtain ⟨U, V, N, m_cap, s_fix, rfl, hu_fit, hq_lt, hv_lt, henv, hcpl, hslot,
      hb, hm, htot, hm_cap, hold⟩ := h
    have hfit_meta : Fits w (metaBase + offCompItems U w N) :=
      lt_of_le_of_lt henv.meta_le_frontier hmem.1
    have hcp_fit := fits_mkCompParams (U := U) (V := V) (w := w) (N := N)
      henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_meta
    have hq_eq : keyQuotient (bucketBits N) u = u >>> bucketBits N :=
      (Nat.shiftRight_eq_div_pow u (bucketBits N)).symm)
  · dsimp only; exact ⟨hu_fit, hcp_fit ⟨20, by decide⟩⟩
  · rw [clientState_compExtractQuotGenProg]
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, henv.meta_le_frontier, hslot, hb⟩
  · rw [clientState_readCompBucketCountGenProg, clientState_compExtractQuotGenProg,
      clientResult_compExtractQuotGenProg, hq_eq]
    exact ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt, hv_lt⟩
  · rw [clientState_compExtractQuotGenProg, clientResult_compExtractQuotGenProg,
      clientState_readCompBucketCountGenProg]
    have hq_lt' : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N := by rwa [hq_eq]
    obtain ⟨hfr_pb, -, _⟩ :=
      compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
    have hlm_s₁ := compLmAt_pushBackSlot_eq henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
    exact ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr_pb.frontier_eq.symm ▸ henv.meta_le_frontier, hb, hm, by rw [hlm_s₁]; exact hold⟩

theorem validProg_compInsertAppendNewGen {w : ℕ}
    {d : ((CompParams × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)} {s : Memory.State}
    (h : CompInsertAppendNewPre w d s) :
    ValidProg w 0 s (compInsertAppendNewGenProg d) := by
  rcases d with ⟨⟨⟨cp, ⟨metaBase, itemBase⟩⟩, ⟨b, m⟩⟩, ⟨u, v⟩⟩
  obtain ⟨U, V, N, m_cap, s_fix, rfl, _hu_fit, hq_lt, hv_lt, henv, hcpl, hslot,
    hb, hm, htot, hm_cap, hold⟩ := h
  have hq_eq : keyQuotient (bucketBits N) u = u >>> bucketBits N :=
    (Nat.shiftRight_eq_div_pow u (bucketBits N)).symm
  have hq_lt' : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N := by rwa [hq_eq]
  dsimp only [compInsertAppendNewGenProg]
  refine validProg_bind (validProg_compExtractQuotGen _ _) ?_
  rw [clientState_compExtractQuotGenProg, clientResult_compExtractQuotGenProg]
  refine validProg_bind
    (validProg_readCompBucketCountGen
      ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
        rfl, henv.meta_le_frontier, hslot, hb⟩) ?_
  rw [clientState_readCompBucketCountGenProg, clientResult_readCompBucketCountGenProg hb]
  refine validProg_bind
    (validProg_compPushBackSlotGen
      ⟨U, V, N, m_cap, s_fix, rfl, henv, hcpl, hslot, hb, htot, hm_cap, hq_lt', hv_lt⟩) ?_
  obtain ⟨hfr_pb, -, _⟩ :=
    compPushBackSlotGenProg_effect henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
  have hlm_s₁ := compLmAt_pushBackSlot_eq henv hcpl hslot hb htot hm_cap hq_lt' hv_lt
  exact validProg_compPrependIfIndexedGen
    ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V,
      rfl, hfr_pb.frontier_eq.symm ▸ henv.meta_le_frontier, hb, hm, by rw [hlm_s₁]; exact hold⟩


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
