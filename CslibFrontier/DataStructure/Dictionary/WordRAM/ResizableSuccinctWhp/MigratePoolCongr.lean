/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateMetaCongr
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
-- Retain private `import all` solely to unfold unexposed `Memory.Prog` bodies in the pool and
-- fallback modules without modifying upstream modules or invalidating cached `.olean` artifacts.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallRegime
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import Mathlib.Tactic.Ring

/-!
# Pool, Fallback, and Source-Slot Congruence (`MigratePoolCongr`)

This module extends `MigrateMetaCongr` along two axes needed for Phase-`6..8` congruence:

1. **Direct-mode (`usePaged = 0`) region confinement (`ConfinedTo M`):** certifies state-free
   confinement for `oddMulReducedProg`, `evalSaltedBoundedProg`, `feistelSplitBoundedProg`,
   `feistelReconBoundedProg`, `bpInitZeroedProg`, `SlotIoLayout` (`usePaged = 0`), `SmallRegime`,
   `LargeBlockPool`, and `FallbackPool` operations.
2. **Paged source-slot coupling (`SlotStateCoupled`, `SlotCoupledStep`):** couples two memory states
   `(s₁, s₂)` agreeing on a metadata region `M` (disjoint from `io.OwnsAddr`) and on the virtual
   pair array `slotIoPairAt io · idx` (`idx < n`) for a source slot (`io.sideBit = 0`), and proves
   congruent execution of `smallEpochDeleteRawProg`, `smallEpochPopAnyRawProg`, `bpReadAtRawProg`,
   `bpWriteAtRawProg`, `bpPopBktBackRawProg`, `fallbackDeleteProg`, and `fallbackPopAnyProg`.

## Main definitions

* `FeistelConf`, `SlotIoDirectConf`: region-confinement bundles for hash seeds and direct `SlotIo`.
* `SlotStateCoupled`, `SlotCoupledStep`: virtual-slot + metadata coupling for `io.sideBit = 0`.

## Main results

* `confinedTo_evalSaltedBoundedProg`, `confinedTo_feistelSplitBoundedProg`,
  `confinedTo_feistelReconBoundedProg`
* `confinedTo_smallEpochInsertRawProg`, `confinedTo_smallEpochDeleteRawProg`,
  `confinedTo_bpWriteAtRawProg`, `confinedTo_bpAppendRawProg`, `confinedTo_bpPopBktBackRawProg`,
  `confinedTo_enterFallbackProg`, `confinedTo_fallbackInsertProg`, `confinedTo_fallbackDeleteProg`
* `smallEpochDeleteRaw_coupled`, `smallEpochPopAnyRaw_coupled`,
  `bpReadAtRaw_coupled`, `bpWriteAtRaw_coupled`, `bpPopBktBackRaw_coupled`,
  `fallbackDelete_coupled`, `fallbackPopAny_coupled`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Hash Evaluators, `bpInitZeroedProg`, and Direct `SlotIo` (`ConfinedTo`) -/

/-- `oddMulReducedProg` is pure and confined to any region `M`. -/
theorem confinedTo_oddMulReducedProg (M : ℕ → Prop) (x : (ℕ × ℕ) × (ℕ × ℕ)) :
    ConfinedTo M (oddMulReducedProg x) := by
  rcases x with ⟨⟨w₀, R_bits⟩, ⟨α_val, u_val⟩⟩
  refine ConfinedTo.of_readOnly (clientState_oddMulReducedProg _) fun s₁ s₂ _ => ?_
  rw [clientResult_oddMulReducedProg, clientResult_oddMulReducedProg]

/-- Bundle certifying that a `FeistelHashCtx` seed table lies inside `M`. -/
@[expose] def FeistelConf (M : ℕ → Prop) : FeistelHashCtx → Prop
  | (((hashBase, offBot_v), (wVal, _w₀)), ((_R_bits, c_tab), (d_tab, (b_char, M_out)))) =>
    0 < wVal ∧
    offBot_v = BitPackedDoubleTabulation.offBot wVal c_tab d_tab b_char ∧
    ∀ addr, hashBase ≤ addr →
      addr < hashBase + BitPackedDoubleTabulation.space wVal c_tab d_tab b_char M_out → M addr

private theorem clientState_dtInnerStep (ctx : DtInnerCtx) (acc : DtInnerAcc)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (dtInnerStepProg (ctx, acc)) = s := by
  rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩
  rcases acc with ⟨⟨_, _⟩, _⟩
  unfold dtInnerStepProg; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]; rfl

private theorem clientState_dtInnerIterate (ctx : DtInnerCtx) (m : ℕ) (acc : DtInnerAcc)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (iterate dtInnerStepProg ctx m acc) = s := by
  rcases acc with ⟨⟨i0, y0⟩, r0⟩
  suffices h0 : ∀ k i y r,
      (Memory.spec 0).clientState s (iterate dtInnerStepProg ctx k ((i, y), r)) = s
    from h0 m i0 y0 r0
  intro k; induction k with
  | zero => intro _ _ _; rfl
  | succ k ihk =>
    intro i y r; unfold iterate
    rw [StateTransitionSpec.clientState_bind, clientState_dtInnerStep]
    rcases (Memory.spec 0).clientResult s (dtInnerStepProg (ctx, ((i, y), r))) with
      ⟨⟨i1, y1⟩, r1⟩
    exact ihk i1 y1 r1

private theorem clientState_dtInnerLoopProg (arg : (DtInnerCtx × DtInnerAcc) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (dtInnerLoopProg arg) = s := by
  rcases arg with ⟨⟨ctx, acc⟩, m⟩
  exact clientState_dtInnerIterate ctx m acc s

private theorem cf_dtInnerLoop {M : ℕ → Prop} {hashBase wVal c_tab d_tab b_char j : ℕ}
    (hw : 0 < wVal) (hj : j < d_tab)
    (htop : ∀ addr, hashBase + 1 ≤ addr →
      addr < hashBase + 1 + BitPackedDoubleTabulation.topWords wVal c_tab d_tab b_char → M addr) :
    ∀ m i y r, i + m ≤ c_tab →
      ConfinedTo M
        (iterate dtInnerStepProg (((hashBase, wVal), (c_tab, b_char)), j) m ((i, y), r)) := by
  intro m
  induction m with
  | zero => intro _ _ _ _; exact ConfinedTo.pure_prog _
  | succ m ih =>
    intro i y r him
    have hi : i < c_tab := by omega
    have hstep : ConfinedTo M
        (dtInnerStepProg ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y), r))) := by
      unfold dtInnerStepProg; simp only [pure_bind]
      have hpow : 1 <<< b_char = 2 ^ b_char := by rw [Nat.shiftLeft_eq, one_mul]
      have hch : r &&& (2 ^ b_char - 1) < 2 ^ b_char := by
        rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hrow : j * (c_tab + 1) + i < d_tab * (c_tab + 1) := by
        calc j * (c_tab + 1) + i
            < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
          _ = (j + 1) * (c_tab + 1) := by ring
          _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
      have hidx : (j * (c_tab + 1) + i) * (1 <<< b_char) + (r &&& ((1 <<< b_char) - 1)) <
          BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
        rw [hpow]
        calc (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1))
            < (j * (c_tab + 1) + i) * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hch _
          _ = (j * (c_tab + 1) + i + 1) * 2 ^ b_char := by ring
          _ ≤ (d_tab * (c_tab + 1)) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow
          _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
              unfold BitPackedDoubleTabulation.topEntries; ring
      exact ConfinedTo.bind_prog (ConfinedTo.readPackedComp_prog hw hidx htop)
        fun _ => ConfinedTo.pure_prog _
    have hst_eq := clientState_dtInnerStep
      ((((hashBase, wVal), (c_tab, b_char)), j)) ((i, y), r)
    have hres_i : ∀ s,
        ((Memory.spec 0).clientResult s
          (dtInnerStepProg ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y), r)))).1.1 =
          i + 1 := fun s => by simp [dtInnerStepProg, prog_clientResult_map]
    refine ConfinedTo.of_readOnly
      (clientState_dtInnerIterate (((hashBase, wVal), (c_tab, b_char)), j) (m + 1) ((i, y), r))
      fun s₁ s₂ hmem => ?_
    unfold iterate
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      hst_eq, hst_eq, ← hstep.res_eq s₁ s₂ hmem]
    rcases h : (Memory.spec 0).clientResult s₁
      (dtInnerStepProg ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y), r))) with
      ⟨⟨i', y'⟩, r'⟩
    have hi' : i' = i + 1 := by have := hres_i s₁; rw [h] at this; exact this
    exact (ih i' y' r' (by omega)).res_eq s₁ s₂ hmem

private theorem dtInnerLoop_y_lt {hashBase wVal c_tab b_char j : ℕ}
    (s : Memory.State) :
    ∀ m i y r, y < 2 ^ b_char →
      let ((_, y'), _) := (Memory.spec 0).clientResult s
        (iterate dtInnerStepProg (((hashBase, wVal), (c_tab, b_char)), j) m ((i, y), r))
      y' < 2 ^ b_char := by
  intro m
  induction m with
  | zero => intro _ y _ hy; exact hy
  | succ m ih =>
    intro i y r hy
    unfold iterate
    have hst := clientState_dtInnerStep
      ((((hashBase, wVal), (c_tab, b_char)), j)) ((i, y), r) s
    have hy1 :
        let ((_, y1), _) := (Memory.spec 0).clientResult s
          (dtInnerStepProg ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y), r)))
        y1 < 2 ^ b_char := by
      unfold dtInnerStepProg
      simp only [pure_bind, prog_clientResult_bind, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, prog_clientResult_pure]
      exact Nat.xor_lt_two_pow hy (readPacked_lt ..)
    rw [StateTransitionSpec.clientResult_bind, hst]
    rcases h : (Memory.spec 0).clientResult s
      (dtInnerStepProg ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y), r))) with
      ⟨⟨i1, y1⟩, r1⟩
    rw [h] at hy1
    exact ih i1 y1 r1 hy1

private theorem clientState_dtOuterStepProg (octx : DtOuterCtx) (acc : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (dtOuterStepProg (octx, acc)) = s := by
  rcases octx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  rcases acc with ⟨_, _⟩
  unfold dtOuterStepProg; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_dtInnerLoopProg]
  rcases (Memory.spec 0).clientResult s (dtInnerLoopProg _) with ⟨⟨_, _⟩, _⟩
  rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg,
    StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
  rfl

/-- `evalSaltedBoundedProg` is confined to `M` when `FeistelConf M ctx` and `s_val < 2 ^ b_char`.
-/
theorem confinedTo_evalSaltedBoundedProg {M : ℕ → Prop} {ctx : FeistelHashCtx} {s_val u_val : ℕ}
    (h : FeistelConf M ctx)
    (hs : let (_, (_, (_, (b_char, _)))) := ctx; s_val < 2 ^ b_char) :
    ConfinedTo M (evalSaltedBoundedProg (ctx, (s_val, u_val))) := by
  rcases ctx with ⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩, ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, M_out⟩⟩⟩⟩
  obtain ⟨hw, hoff, hsub⟩ := h
  dsimp only at hs
  have hsp_pos := BitPackedDoubleTabulation.space_pos wVal c_tab d_tab b_char M_out
  have hm_hb : M hashBase := hsub hashBase le_rfl (by omega)
  have htop : ∀ addr, hashBase + 1 ≤ addr →
      addr < hashBase + 1 + BitPackedDoubleTabulation.topWords wVal c_tab d_tab b_char → M addr :=
    fun addr h1 h2 => hsub addr (by omega) (by unfold BitPackedDoubleTabulation.space; omega)
  have hbot : ∀ addr, hashBase + offBot_v ≤ addr →
      addr < hashBase + offBot_v + BitPackedDoubleTabulation.botWords wVal d_tab b_char M_out →
      M addr := fun addr h1 h2 => by
    subst hoff
    exact hsub addr (by omega)
      (by unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.offBot at *; omega)
  unfold evalSaltedBoundedProg dtOuterLoopProg
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog hm_hb) fun α_val =>
    ConfinedTo.bind_prog (confinedTo_oddMulReducedProg M _) fun rKey => ?_
  simp only [pure_bind]
  suffices hout : ∀ m j out, j + m ≤ d_tab →
      ConfinedTo M (iterate dtOuterStepProg
        (((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, rKey))) m (j, out)) from
    ConfinedTo.bind_prog (hout d_tab 0 0 (Nat.zero_add _).le) fun _ => ConfinedTo.pure_prog _
  intro m
  induction m with
  | zero => intro _ _ _; exact ConfinedTo.pure_prog _
  | succ m ih =>
    intro j out hjm
    have hj : j < d_tab := by omega
    have hpow : 1 <<< b_char = 2 ^ b_char := by rw [Nat.shiftLeft_eq, one_mul]
    have hrow_s : j * (c_tab + 1) + c_tab < d_tab * (c_tab + 1) := by
      calc j * (c_tab + 1) + c_tab
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
    have hidx_s : (j * (c_tab + 1) + c_tab) * (1 <<< b_char) + s_val <
        BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
      rw [hpow]
      calc (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val
          < (j * (c_tab + 1) + c_tab) * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hs _
        _ = (j * (c_tab + 1) + c_tab + 1) * 2 ^ b_char := by ring
        _ ≤ (d_tab * (c_tab + 1)) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow_s
        _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
            unfold BitPackedDoubleTabulation.topEntries; ring
    let octx : DtOuterCtx :=
      (((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, rKey)))
    have hin_cf := cf_dtInnerLoop hw hj htop c_tab 0 0 rKey (Nat.zero_add _).le
    have hin_st : ∀ s, (Memory.spec 0).clientState s
        (dtInnerLoopProg
          (((((hashBase, wVal), (c_tab, b_char)), j), ((0, 0), rKey)), c_tab)) = s :=
      clientState_dtInnerLoopProg _
    have hstep_st : ∀ s, (Memory.spec 0).clientState s (dtOuterStepProg (octx, (j, out))) = s :=
      clientState_dtOuterStepProg octx (j, out)
    have hstep_cf : ConfinedTo M (dtOuterStepProg (octx, (j, out))) := by
      refine ConfinedTo.of_readOnly hstep_st fun s₁ s₂ hmem => ?_
      have hres_in := hin_cf.res_eq s₁ s₂ hmem
      have hy_lt := dtInnerLoop_y_lt (hashBase := hashBase) (wVal := wVal) (c_tab := c_tab)
        (b_char := b_char) (j := j) s₁ c_tab 0 0 rKey (Nat.two_pow_pos b_char)
      have hs1 := hin_st s₁; have hs2 := hin_st s₂
      unfold dtInnerLoopProg at hs1 hs2
      dsimp only at hs1 hs2
      unfold dtOuterStepProg dtInnerLoopProg; dsimp only [octx]; simp only [pure_bind]
      conv_lhs => rw [StateTransitionSpec.clientResult_bind, hs1]
      conv_rhs => rw [StateTransitionSpec.clientResult_bind, hs2, ← hres_in]
      rcases hr : (Memory.spec 0).clientResult s₁
        (iterate dtInnerStepProg (((hashBase, wVal), (c_tab, b_char)), j) c_tab ((0, 0), rKey)) with
        ⟨⟨iF, y_acc⟩, rF⟩
      rw [hr] at hy_lt
      have hts := (ConfinedTo.readPackedComp_prog hw hidx_s htop).res_eq s₁ s₂ hmem
      conv_lhs => rw [StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg]
      conv_rhs =>
        rw [StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg, ← hts]
      set t_salt := (Memory.spec 0).clientResult s₁
        (readPackedCompGenProg (((hashBase, 1), (b_char, wVal)),
          (j * (c_tab + 1) + c_tab) * (1 <<< b_char) + s_val))
      have hts_lt : t_salt < 2 ^ b_char := by
        dsimp only [t_salt]; rw [clientResult_readPackedCompGenProg]; exact readPacked_lt ..
      have hyj_lt : y_acc ^^^ t_salt < 2 ^ b_char := Nat.xor_lt_two_pow hy_lt hts_lt
      have hidx₂ : j * (1 <<< b_char) + (y_acc ^^^ t_salt) <
          BitPackedDoubleTabulation.botEntries d_tab b_char := by
        rw [hpow]
        calc j * 2 ^ b_char + (y_acc ^^^ t_salt)
            < j * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hyj_lt _
          _ = (j + 1) * 2 ^ b_char := by ring
          _ ≤ d_tab * 2 ^ b_char := Nat.mul_le_mul_right _ hj
      have hzj := (ConfinedTo.readPackedComp_prog hw hidx₂ hbot).res_eq s₁ s₂ hmem
      conv_lhs => rw [StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg]
      conv_rhs =>
        rw [StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg, ← hzj]
      rfl
    have hstep_j : ∀ s,
        ((Memory.spec 0).clientResult s (dtOuterStepProg (octx, (j, out)))).1 = j + 1 := by
      intro s
      have hs_in := hin_st s
      unfold dtOuterStepProg; simp only [pure_bind]
      rw [StateTransitionSpec.clientResult_bind, hs_in]
      rcases (Memory.spec 0).clientResult s
        (dtInnerLoopProg
          (((((hashBase, wVal), (c_tab, b_char)), j), ((0, 0), rKey)), c_tab)) with
        ⟨⟨_, _⟩, _⟩
      rw [StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg,
        StateTransitionSpec.clientResult_bind, clientState_readPackedCompGenProg]
      rfl
    unfold iterate
    exact {
      fr_eq := fun s => by
        rw [StateTransitionSpec.clientState_bind, hstep_st]
        rcases h : (Memory.spec 0).clientResult s (dtOuterStepProg (octx, (j, out))) with ⟨j', o'⟩
        have hj' : j' = j + 1 := by have := hstep_j s; rw [h] at this; exact this
        exact (ih j' o' (by omega)).fr_eq s
      mem_out := fun s addr hnot => by
        rw [StateTransitionSpec.clientState_bind, hstep_st]
        rcases h : (Memory.spec 0).clientResult s (dtOuterStepProg (octx, (j, out))) with ⟨j', o'⟩
        have hj' : j' = j + 1 := by have := hstep_j s; rw [h] at this; exact this
        exact (ih j' o' (by omega)).mem_out s addr hnot
      res_eq := fun s₁ s₂ hmem => by
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
          hstep_st, hstep_st, ← hstep_cf.res_eq s₁ s₂ hmem]
        rcases h : (Memory.spec 0).clientResult s₁ (dtOuterStepProg (octx, (j, out))) with ⟨j', o'⟩
        have hj' : j' = j + 1 := by have := hstep_j s₁; rw [h] at this; exact this
        exact (ih j' o' (by omega)).res_eq s₁ s₂ hmem
      mem_in := fun s₁ s₂ hmem addr ha => by
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_st, ← hstep_cf.res_eq s₁ s₂ hmem]
        rcases h : (Memory.spec 0).clientResult s₁ (dtOuterStepProg (octx, (j, out))) with ⟨j', o'⟩
        have hj' : j' = j + 1 := by have := hstep_j s₁; rw [h] at this; exact this
        exact (ih j' o' (by omega)).mem_in s₁ s₂ hmem addr ha
    }

/-- `feistelSplitBoundedProg` is confined to `M` under `FeistelConf M ctx`. -/
theorem confinedTo_feistelSplitBoundedProg {M : ℕ → Prop} {ctx : FeistelHashCtx} {u_val : ℕ}
    (h : FeistelConf M ctx) :
    ConfinedTo M (feistelSplitBoundedProg (ctx, u_val)) := by
  rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨b_char, _⟩⟩⟩⟩
  unfold feistelSplitBoundedProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog
    (confinedTo_evalSaltedBoundedProg h (Nat.two_pow_pos b_char))
    fun _ => ConfinedTo.pure_prog _

/-- `feistelReconBoundedProg` is confined to `M` under `FeistelConf M ctx`. -/
theorem confinedTo_feistelReconBoundedProg {M : ℕ → Prop} {ctx : FeistelHashCtx} {bkt q_val : ℕ}
    (h : FeistelConf M ctx) :
    ConfinedTo M (feistelReconBoundedProg (ctx, (bkt, q_val))) := by
  rcases ctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨b_char, _⟩⟩⟩⟩
  unfold feistelReconBoundedProg
  simp only [pure_bind]
  exact ConfinedTo.bind_prog
    (confinedTo_evalSaltedBoundedProg h (Nat.two_pow_pos b_char))
    fun _ => ConfinedTo.pure_prog _

/-- `readPairGenProg` is confined to `M` whenever `[ib, ib + pairStreamWords nc qb vb wv)` lies in
`M`. -/
private theorem confinedTo_readPairGenProg {M : ℕ → Prop} {ib qb vb wv idx nc : ℕ}
    (hw : 0 < wv) (hidx : idx < nc)
    (hsub : ∀ addr, ib ≤ addr → addr < ib + pairStreamWords nc qb vb wv → M addr) :
    ConfinedTo M (readPairGenProg (((ib, (qb, vb)), wv), idx)) := by
  refine ConfinedTo.of_readOnly (clientState_readPairGenProg _) fun s₁ s₂ h => ?_
  rw [clientResult_readPairGenProg, clientResult_readPairGenProg]
  have hltQ := wOffQ_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
  have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
  have hq0 := h (ib + wOffQ qb vb wv idx) (hsub _ (Nat.le_add_right _ _) (by omega))
  have hq1 := h (ib + wOffQ qb vb wv idx + 1) (hsub _ (by omega) (by omega))
  have hv0 := h (ib + wOffV qb vb wv idx) (hsub _ (Nat.le_add_right _ _) (by omega))
  have hv1 := h (ib + wOffV qb vb wv idx + 1) (hsub _ (by omega) (by omega))
  unfold pairQuotAt pairValAt readBitSlice
  rw [hq0, hq1, hv0, hv1]

/-- `writePairGenProg` is confined to `M` whenever `[ib, ib + pairStreamWords nc qb vb wv)` lies in
`M`. -/
private theorem confinedTo_writePairGenProg {M : ℕ → Prop} {ib qb vb wv idx nc q v : ℕ}
    (hw : 0 < wv) (hidx : idx < nc)
    (hsub : ∀ addr, ib ≤ addr → addr < ib + pairStreamWords nc qb vb wv → M addr) :
    ConfinedTo M (writePairGenProg ((((ib, (qb, vb)), wv), idx), (q, v))) where
  fr_eq s := by rw [clientState_writePairGenProg]
  mem_out s addr hnot := by
    rw [clientState_writePairGenProg]; dsimp only
    exact writePair_outside hw hidx s.mem (fun ha => hnot (hsub addr ha.1 ha.2))
  res_eq _ _ _ := rfl
  mem_in s₁ s₂ h addr ha := by
    rw [clientState_writePairGenProg, clientState_writePairGenProg]; dsimp only
    have hltQ := wOffQ_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
    have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hidx
    have hq0 := h (ib + wOffQ qb vb wv idx) (hsub _ (Nat.le_add_right _ _) (by omega))
    have hq1 := h (ib + wOffQ qb vb wv idx + 1) (hsub _ (by omega) (by omega))
    let aQ0 := ib + wOffQ qb vb wv idx
    let aQ1 := ib + wOffQ qb vb wv idx + 1
    let aV0 := ib + wOffV qb vb wv idx
    let aV1 := ib + wOffV qb vb wv idx + 1
    have hq_mem : ∀ b, M b →
        writePairQuot ib qb vb wv s₁.mem idx q b = writePairQuot ib qb vb wv s₂.mem idx q b := by
      intro b hb
      unfold writePairQuot writeBitSlice
      by_cases h1 : b = aQ1
      · subst h1
        rw [Function.update_self, Function.update_self,
          Function.update_of_ne (by omega), Function.update_of_ne (by omega), hq1]
      · rw [Function.update_of_ne h1, Function.update_of_ne h1]
        by_cases h0 : b = aQ0
        · subst h0; rw [Function.update_self, Function.update_self, hq0]
        · rw [Function.update_of_ne h0, Function.update_of_ne h0, h b hb]
    have hmV0 : M aV0 := hsub _ (Nat.le_add_right _ _) (by omega)
    have hmV1 : M aV1 := hsub _ (by omega) (by omega)
    unfold writePair writePairVal writeBitSlice
    by_cases h1 : addr = aV1
    · subst h1
      rw [Function.update_self, Function.update_self,
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), hq_mem aV1 hmV1]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h0 : addr = aV0
      · subst h0; rw [Function.update_self, Function.update_self, hq_mem aV0 hmV0]
      · rw [Function.update_of_ne h0, Function.update_of_ne h0, hq_mem addr ha]

/-- Bundle certifying that `ioctx : SlotIoCtx` is in direct (`usePaged = 0`) mode with its owned
addresses inside `M`. -/
@[expose] def SlotIoDirectConf (M : ℕ → Prop) (ioctx : SlotIoCtx) : Prop :=
  let io := SlotIoLayout.ofCtx ioctx
  io.usePaged = 0 ∧ 0 < io.pgL.w ∧ ∀ addr, io.OwnsAddr addr → M addr

/-- `slotIoReadRawProg` is confined to `M` under `SlotIoDirectConf M ioctx`. -/
private theorem confinedTo_slotIoReadRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {idx : ℕ}
    (h : SlotIoDirectConf M ioctx) :
    ConfinedTo M (slotIoReadRawProg (ioctx, idx)) := by
  rcases ioctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  obtain ⟨hup, hw, hM⟩ := h
  dsimp only [SlotIoLayout.ofCtx] at hup hw hM
  unfold slotIoReadRawProg; dsimp only
  rw [ite_eq_left hup]
  refine ConfinedTo.ite_prog (fun hidx => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun hsb => ?_) (fun hsb => ?_)
  · exact confinedTo_readPairGenProg hw hidx fun addr h1 h2 =>
      hM addr (by
        unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_left hsb]; exact ⟨h1, h2⟩)
  · refine ConfinedTo.bind_prog (ConfinedTo.read_prog (hM mb (by
        unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]; exact Or.inl rfl)))
      fun sp => ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
    · exact confinedTo_readPairGenProg hw hidx fun addr h1 h2 =>
        hM addr (by
          unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]
          exact Or.inr (Or.inl ⟨h1, h2⟩))
    · refine ConfinedTo.bind_prog (confinedTo_readPairGenProg hw hidx fun addr h1 h2 =>
          hM addr (by
            unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]
            exact Or.inr (Or.inr ⟨h1, h2⟩))) fun _ => ?_
      exact ConfinedTo.ite_prog
        (fun _ => ConfinedTo.bind_prog (ConfinedTo.pure_prog _) fun _ => ConfinedTo.pure_prog _)
        (fun _ => ConfinedTo.pure_prog _)

/-- `slotIoWriteRawProg` is confined to `M` under `SlotIoDirectConf M ioctx`. -/
private theorem confinedTo_slotIoWriteRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {idx : ℕ}
    {qv : ℕ × ℕ} (h : SlotIoDirectConf M ioctx) :
    ConfinedTo M (slotIoWriteRawProg ((ioctx, idx), qv)) := by
  rcases ioctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  rcases qv with ⟨q, v⟩
  obtain ⟨hup, hw, hM⟩ := h
  dsimp only [SlotIoLayout.ofCtx] at hup hw hM
  unfold slotIoWriteRawProg; dsimp only
  rw [ite_eq_left hup]
  refine ConfinedTo.ite_prog (fun hidx => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun hsb => ?_) (fun hsb => ?_)
  · exact confinedTo_writePairGenProg hw hidx fun addr h1 h2 =>
      hM addr (by
        unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_left hsb]; exact ⟨h1, h2⟩)
  · refine ConfinedTo.bind_prog (ConfinedTo.read_prog (hM mb (by
        unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]; exact Or.inl rfl)))
      fun sp => ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ?_)
    · exact confinedTo_writePairGenProg hw hidx fun addr h1 h2 =>
        hM addr (by
          unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]
          exact Or.inr (Or.inl ⟨h1, h2⟩))
    · exact confinedTo_writePairGenProg hw hidx fun addr h1 h2 =>
        hM addr (by
          unfold SlotIoLayout.OwnsAddr; rw [ite_eq_left hup, ite_eq_right hsb]
          exact Or.inr (Or.inr ⟨h1, h2⟩))

/-- `slotIoSwapRawProg` is confined to `M` under `SlotIoDirectConf M ioctx`. -/
private theorem confinedTo_slotIoSwapRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {p₁ p₂ : ℕ}
    (h : SlotIoDirectConf M ioctx) :
    ConfinedTo M (slotIoSwapRawProg (ioctx, (p₁, p₂))) := by
  unfold slotIoSwapRawProg
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) fun _ => ?_
  exact ConfinedTo.bind_prog (confinedTo_slotIoReadRawProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoReadRawProg h) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoWriteRawProg h) fun _ =>
    confinedTo_slotIoWriteRawProg h

/-- `slotIoAppendRawProg` is confined to `M` under `SlotIoDirectConf M ioctx`. -/
private theorem confinedTo_slotIoAppendRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {nSide : ℕ}
    {qv : ℕ × ℕ} (h : SlotIoDirectConf M ioctx) :
    ConfinedTo M (slotIoAppendRawProg ((ioctx, nSide), qv)) := by
  have hw := confinedTo_slotIoWriteRawProg (idx := nSide) (qv := qv) h
  rcases ioctx with ⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩
  rcases qv with ⟨q, v⟩
  have hup : up = 0 := h.1
  unfold slotIoWriteRawProg at hw; unfold slotIoAppendRawProg; dsimp only at hw ⊢
  rw [ite_eq_left hup] at hw ⊢; exact hw

/-- `slotIoPopBackRawProg` is confined to `M` under `SlotIoDirectConf M ioctx`. -/
private theorem confinedTo_slotIoPopBackRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx}
    (h : SlotIoDirectConf M ioctx) :
    ConfinedTo M (slotIoPopBackRawProg ioctx) := by
  rcases ioctx with ⟨⟨up, sb⟩, pctx⟩
  obtain ⟨hup, _, _⟩ := h
  dsimp only [SlotIoLayout.ofCtx] at hup
  unfold slotIoPopBackRawProg; dsimp only
  rw [ite_eq_left hup]
  exact ConfinedTo.pure_prog _

/-! ## Section 2: Direct (`usePaged = 0`) `SmallRegime`, `LargeBlockPool`, and `FallbackPool` -/

private theorem cf_smallEpochScanRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {mb u_key : ℕ}
    (h0 : M mb) (h1 : M (mb + 1)) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (smallEpochScanRawProg ((ioctx, mb), u_key)) := by
  rcases ioctx with ⟨p1, ⟨p2, ⟨p3, nCap⟩⟩⟩
  unfold smallEpochScanRawProg
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog h1) fun nSide => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.bind_prog ?_ fun _ => ConfinedTo.pure_prog _
  unfold smallEpochScanLoopProg
  refine ConfinedTo.iterate_prog _ (fun acc => ?_) nSide _
  rcases acc with ⟨⟨cur, found⟩, ⟨hitIdx, hitVal⟩⟩
  unfold smallEpochScanStepProg
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog h0) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (confinedTo_slotIoReadRawProg hio) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

/-- `smallEpochInsertRawProg` is confined to `M` under `M mb ∧ M (mb + 1) ∧ SlotIoDirectConf`. -/
theorem confinedTo_smallEpochInsertRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {mb u_key v_val : ℕ}
    (h0 : M mb) (h1 : M (mb + 1)) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (smallEpochInsertRawProg (((ioctx, mb), u_key), v_val)) := by
  rcases ioctx with ⟨p1, ⟨p2, ⟨p3, nCap⟩⟩⟩
  unfold smallEpochInsertRawProg
  refine ConfinedTo.bind_prog (cf_smallEpochScanRawProg h0 h1 hio) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => confinedTo_slotIoWriteRawProg hio) fun _ => ?_
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog h1) fun nSide => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (confinedTo_slotIoAppendRawProg hio) fun _ =>
    ConfinedTo.write_prog h1 (nSide + 1)

/-- `smallEpochDeleteRawProg` is confined to `M` under `M mb ∧ M (mb + 1) ∧ SlotIoDirectConf`. -/
theorem confinedTo_smallEpochDeleteRawProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {mb u_key : ℕ}
    (h0 : M mb) (h1 : M (mb + 1)) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (smallEpochDeleteRawProg ((ioctx, mb), u_key)) := by
  unfold smallEpochDeleteRawProg
  refine ConfinedTo.bind_prog (cf_smallEpochScanRawProg h0 h1 hio) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (ConfinedTo.read_prog h1) fun nSide => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_slotIoSwapRawProg hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoPopBackRawProg hio) fun _ =>
    ConfinedTo.write_prog h1 (nSide - 1)

private theorem cf_bpExecOptSwapProg {M : ℕ → Prop} {ioctx : SlotIoCtx} {osw : ℕ × (ℕ × ℕ)}
    (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpExecOptSwapProg (ioctx, osw)) := by
  rcases osw with ⟨hasSw, ⟨p₁, p₂⟩⟩
  unfold bpExecOptSwapProg
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _)
    (fun _ => confinedTo_slotIoSwapRawProg hio)

private theorem confinedTo_bpRunBktTicks16Prog {M : ℕ → Prop} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {b : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpRunBktTicks16Prog ((mctx, ioctx), b)) := by
  have h1 : ConfinedTo M (bpBktTickStepProg ((mctx, ioctx), b)) :=
    ConfinedTo.bind_prog (confinedTo_bpBktTickMetaProg hm) fun _ => cf_bpExecOptSwapProg hio
  have h2 := ConfinedTo.bind_prog h1 fun _ => h1
  have h4 := ConfinedTo.bind_prog h2 fun _ => h2
  have h8 := ConfinedTo.bind_prog h4 fun _ => h4
  exact ConfinedTo.bind_prog h8 fun _ => h8

private theorem confinedTo_bpRunTopClean16Prog {M : ℕ → Prop} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpRunTopClean16Prog (mctx, ioctx)) := by
  have h1 : ConfinedTo M (bpTopCleanStepProg (mctx, ioctx)) :=
    ConfinedTo.bind_prog (confinedTo_bpTopCleanMetaProg hm) fun _ => cf_bpExecOptSwapProg hio
  have h2 := ConfinedTo.bind_prog h1 fun _ => h1
  have h4 := ConfinedTo.bind_prog h2 fun _ => h2
  have h8 := ConfinedTo.bind_prog h4 fun _ => h4
  exact ConfinedTo.bind_prog h8 fun _ => h8

/-- `bpReadAtRawProg` is confined to `M` under `BpMetaConf` and `SlotIoDirectConf`. -/
theorem confinedTo_bpReadAtRawProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b loc : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpReadAtRawProg ((mctx, ioctx), (b, loc))) := by
  unfold bpReadAtRawProg
  exact ConfinedTo.bind_prog (confinedTo_bpToPhysProg hm) fun _ => confinedTo_slotIoReadRawProg hio

/-- `bpWriteAtRawProg` is confined to `M` under `BpMetaConf` and `SlotIoDirectConf`. -/
theorem confinedTo_bpWriteAtRawProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b loc : ℕ} {qv : ℕ × ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpWriteAtRawProg (((mctx, ioctx), (b, loc)), qv)) := by
  unfold bpWriteAtRawProg
  exact ConfinedTo.bind_prog (confinedTo_bpToPhysProg hm) fun _ => confinedTo_slotIoWriteRawProg hio

/-- `bpAppendRawProg` is confined to `M` under `BpMetaConf` and `SlotIoDirectConf`. -/
theorem confinedTo_bpAppendRawProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {qv : ℕ × ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpAppendRawProg (((mctx, ioctx), b), qv)) := by
  unfold bpAppendRawProg
  exact ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoAppendRawProg hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpRawPostAppendMetaProg hm) fun _ =>
    confinedTo_bpRunBktTicks16Prog hm hio

/-- `bpPopBktBackRawProg` is confined to `M` under `BpMetaConf` and `SlotIoDirectConf`. -/
theorem confinedTo_bpPopBktBackRawProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (bpPopBktBackRawProg ((mctx, ioctx), b)) := by
  unfold bpPopBktBackRawProg bpPopBktPrepAndShrinkProg
  exact ConfinedTo.bind_prog
    (ConfinedTo.bind_prog (confinedTo_bpPrepPopMetaProg hm) fun _ =>
      ConfinedTo.bind_prog (cf_bpExecOptSwapProg hio) fun _ =>
      ConfinedTo.bind_prog (confinedTo_slotIoPopBackRawProg hio) fun _ =>
      confinedTo_bpCommitPopMetaProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpRunBktTicks16Prog hm hio) fun _ =>
    confinedTo_bpRunTopClean16Prog hm hio

private theorem cf_fbOwnerOfProg {M : ℕ → Prop} {mctx : BpMetaCtx} {p : ℕ}
    (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbOwnerOfProg (mctx, p)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nc⟩⟩⟩
  unfold fbOwnerOfProg fbOwnerOfProg.bpGetMKFromCtxProg fbOwnerOfProg.bpGetNcapFromCtxProg
  simp only [pure_bind]
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => confinedTo_bpReadSlabOwnerProg hm) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact confinedTo_bpReadTailDirRawProg hm

private theorem cf_fbScanProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {bkt q_u : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbScanProg ((mctx, ioctx), (bkt, q_u))) := by
  rcases mctx with ⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩
  unfold fbScanProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun nSide => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.bind_prog ?_ fun _ => ConfinedTo.pure_prog _
  unfold fbScanLoopProg
  refine ConfinedTo.iterate_prog _ (fun acc => ?_) nSide _
  rcases acc with ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩
  unfold fbScanStepProg
  refine ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (cf_fbOwnerOfProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoReadRawProg hio) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_fbSwapRangeProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b₁ b₂ len : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbSwapRangeProg (((mctx, ioctx), (b₁, b₂)), len)) := by
  rcases mctx with ⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩
  unfold fbSwapRangeProg fbSwapRangeLoopProg; simp only [pure_bind]
  refine ConfinedTo.bind_prog ?_ fun _ => ConfinedTo.pure_prog _
  refine ConfinedTo.iterate_prog _ (fun cur => ?_) len 0
  unfold fbSwapRangeStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _))
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_slotIoSwapRawProg hio) fun _ => ConfinedTo.pure_prog _

private theorem cf_fbSwapTailSlotsProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fbBase t₁ t₂ : ℕ} (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbSwapTailSlotsProg (((mctx, ioctx), fbBase), (t₁, t₂))) := by
  rcases mctx with ⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩
  unfold fbSwapTailSlotsProg fbReadTailPairProg fbWriteTailPairProg
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _))
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog
    (ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ => ConfinedTo.pure_prog _)
    fun _ => ConfinedTo.bind_prog (confinedTo_slotIoSwapRawProg hio) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ =>
      confinedTo_bpWriteTailDirRawProg hm

private theorem cf_fbCountBktLoopProg {M : ℕ → Prop} {mctx : BpMetaCtx} {tl b fuel : ℕ}
    (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbCountBktLoopProg (((mctx, (tl, b)), (0, 0)), fuel)) := by
  rcases mctx with ⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩
  unfold fbCountBktLoopProg
  refine ConfinedTo.iterate_prog _ (fun ⟨t, cnt⟩ => ?_) fuel (0, 0)
  unfold fbCountBktStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_fbFindHeavyBktLoopProg {M : ℕ → Prop} {mctx : BpMetaCtx} {tl fuel : ℕ}
    (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbFindHeavyBktLoopProg (((mctx, tl), (0, 0)), fuel)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbFindHeavyBktLoopProg
  refine ConfinedTo.iterate_prog _ (fun ⟨b, bStar⟩ => ?_) fuel (0, 0)
  unfold fbFindHeavyBktStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_fbCountBktLoopProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_fbFindMatchLoopProg {M : ℕ → Prop} {mctx : BpMetaCtx}
    {tl bS dst fuel : ℕ} (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbFindMatchLoopProg (((mctx, (tl, bS)), (dst, (0, dst))), fuel)) := by
  unfold fbFindMatchLoopProg
  refine ConfinedTo.iterate_prog _ (fun ⟨t, ⟨found, src⟩⟩ => ?_) fuel _
  unfold fbFindMatchStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => ConfinedTo.pure_prog _)

private theorem cf_fbPromoteFinishProg {M : ℕ → Prop} {mctx : BpMetaCtx} {fb0 tl bStar : ℕ}
    (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbPromoteFinishProg ((mctx, (fb0, tl)), bStar)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbPromoteFinishProg
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg hm) fun _ => ?_
  simp only [pure_bind]
  refine ConfinedTo.bind_prog ?_ fun _ => confinedTo_bpWriteScalarProg hm
  unfold fbShiftLeftLoopProg
  refine ConfinedTo.iterate_prog _ (fun t => ?_) _ 0
  unfold fbShiftLeftStepProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ => ConfinedTo.pure_prog _

private theorem cf_fbPromoteOneBlockProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbPromoteOneBlockProg (mctx, ioctx)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbPromoteOneBlockProg fbPromoteCheckProg fbPromoteInnerCheckProg fbPromoteBodyProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun nSide =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun fb0 => ?_
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (cf_fbFindHeavyBktLoopProg hm) fun hb => ?_
  rcases hb with ⟨_, bStar⟩
  have hph : ConfinedTo M
      (fbPartHeavyLoopProg
        (((((p1, (((m, k), p2b), (mt, nCap))), ioctx),
          (fb0 * k, (nSide - fb0 * k, bStar))), 0), k)) := by
    unfold fbPartHeavyLoopProg
    refine ConfinedTo.iterate_prog _ (fun dst => ?_) k 0
    unfold fbPartHeavyStepProg
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    simp only [pure_bind]
    exact ConfinedTo.bind_prog (cf_fbFindMatchLoopProg hm) fun _ =>
      ConfinedTo.bind_prog (cf_fbSwapTailSlotsProg hm hio) fun _ => ConfinedTo.pure_prog _
  exact ConfinedTo.bind_prog hph fun _ => cf_fbPromoteFinishProg hm

private theorem cf_fbMaybePromoteProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbMaybePromoteProg (mctx, ioctx)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbMaybePromoteProg fbMaybePromoteCheckProg fbMaybePromoteInnerProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog
    (fun _ => cf_fbPromoteOneBlockProg hm hio) (fun _ => ConfinedTo.pure_prog _))
    (fun _ => ConfinedTo.pure_prog _)

private theorem cf_fbDemoteTailProg {M : ℕ → Prop} {mctx : BpMetaCtx} {lb tl b_blk : ℕ}
    (hm : BpMetaConf M mctx) :
    ConfinedTo M (fbDemoteTailProg ((mctx, (lb, tl)), b_blk)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbDemoteTailProg; simp only [pure_bind]
  have hsr : ConfinedTo M
      (fbShiftRightLoopProg ((((p1, (((m, k), p2b), (mt, nCap))), k), tl), tl)) := by
    unfold fbShiftRightLoopProg
    refine ConfinedTo.iterate_prog _ (fun rem => ?_) tl tl
    unfold fbShiftRightStepProg
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ =>
        ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _))
        (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
    simp only [pure_bind]
    exact ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ => ConfinedTo.pure_prog _
  have hfh : ConfinedTo M
      (fbFillHeadLoopProg ((((p1, (((m, k), p2b), (mt, nCap))), b_blk), 0), k)) := by
    unfold fbFillHeadLoopProg
    refine ConfinedTo.iterate_prog _ (fun i => ?_) k 0
    unfold fbFillHeadStepProg
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ =>
      ConfinedTo.pure_prog _
  exact ConfinedTo.bind_prog hsr fun _ =>
    ConfinedTo.bind_prog hfh fun _ => confinedTo_bpWriteScalarProg hm

private theorem cf_fbDemoteBlkProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx} {blk : ℕ}
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbDemoteBlkProg ((mctx, ioctx), blk)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbDemoteBlkProg fbDemoteCheckProg fbDemoteInnerProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  have hsw : ∀ lb, ConfinedTo M
      (fbDemoteSwapProg (((p1, (((m, k), p2b), (mt, nCap))), ioctx), (blk, lb))) := by
    intro lb
    unfold fbDemoteSwapProg fbDemoteSwapBodyProg fbReadBlkPairProg fbWriteBlkPairProg
    refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog
      (ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ => ConfinedTo.pure_prog _)
      fun _ => ConfinedTo.bind_prog (cf_fbSwapRangeProg hm hio) fun _ =>
        ConfinedTo.bind_prog
          (ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg hm) fun _ =>
            confinedTo_bpWriteSlabOwnerProg hm) fun _ => ConfinedTo.pure_prog _
  exact ConfinedTo.bind_prog (hsw _) fun _ => cf_fbDemoteTailProg hm

private theorem cf_fbPopTailAtProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx} {p : ℕ}
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbPopTailAtProg ((mctx, ioctx), p)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbPopTailAtProg fbPopTailCheckProg fbPopTailInnerProg fbPopBackAndDecProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
    (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
  exact ConfinedTo.bind_prog (cf_fbSwapTailSlotsProg hm hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_slotIoPopBackRawProg hio) fun _ =>
    confinedTo_bpWriteScalarProg hm

private theorem cf_fbDeleteSlotProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx} {hitP : ℕ}
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fbDeleteSlotProg ((mctx, ioctx), hitP)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fbDeleteSlotProg fbDemoteAndPopProg fbDemotePopRunProg
  refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun dm => ?_
  rcases dm with ⟨blk, off⟩
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => cf_fbPopTailAtProg hm hio)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.bind_prog (cf_fbMaybePromoteProg hm hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (cf_fbDemoteBlkProg hm hio) fun _ => cf_fbPopTailAtProg hm hio

/-- `enterFallbackProg` is confined to `M` under `M (metaBase + 2)`, `BpMetaConf`, and
`SlotIoDirectConf`. -/
theorem confinedTo_enterFallbackProg {M : ℕ → Prop} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    (hm2 : M ((BpMetaLayout.ofCtx mctx).metaBase + 2))
    (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (enterFallbackProg (mctx, ioctx)) := by
  rcases mctx with ⟨⟨⟨⟨mb, obm⟩, p1b⟩, p1c⟩, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  set mctx0 : BpMetaCtx := ((((mb, obm), p1b), p1c), (((m, k), p2b), (mt, nCap)))
  dsimp only [BpMetaLayout.ofCtx] at hm2
  have hun : ConfinedTo M (fbUndoTopSwapProg (mctx0, ioctx)) := by
    unfold fbUndoTopSwapProg fbUndoTopSwapReadProg fbUndoTopSwapCheckProg fbUndoTopSwapBodyProg
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    exact ConfinedTo.bind_prog (cf_fbSwapRangeProg hm hio) fun _ => confinedTo_bpWriteScalarProg hm
  unfold enterFallbackProg fbEnterCompactAndFinishProg fbCompactAndFinishAtProg fbRunCompactPureProg
    fbCompactPureLoopProg
  refine ConfinedTo.bind_prog hun fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun nSide =>
    ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun dm => ?_
  rcases dm with ⟨bf, _⟩
  simp only [pure_bind]
  have hcp : ConfinedTo M
      (iterate fbCompactPureStepProg ((mctx0, ioctx), bf) bf (0, 0)) := by
    refine ConfinedTo.iterate_prog _ (fun ⟨P, sPure⟩ => ?_) bf (0, 0)
    unfold fbCompactPureStepProg fbCompactPureHitProg fbCompactSwapBlkProg fbCompactSwapBlkBodyProg
      fbCompactDoRangeProg fbSwapSlabMeta3Prog
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    refine ConfinedTo.bind_prog ?_ fun _ => ConfinedTo.pure_prog _
    refine ConfinedTo.ite_prog (fun _ => ConfinedTo.ite_prog (fun _ => ?_)
      (fun _ => ConfinedTo.pure_prog _)) (fun _ => ConfinedTo.pure_prog _)
    simp only [pure_bind]
    have hsl : ∀ ln, ConfinedTo M (fbSwapSlabLaneProg ((mctx0, (sPure, P)), ln)) := fun _ => by
      unfold fbSwapSlabLaneProg fbReadSlabLanePairProg fbWriteSlabLanePairProg
      exact ConfinedTo.bind_prog
        (ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
          ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ => ConfinedTo.pure_prog _)
        fun ⟨_, _⟩ => ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg hm) fun _ =>
          confinedTo_bpWriteSlabOwnerProg hm
    exact ConfinedTo.bind_prog (cf_fbSwapRangeProg hm hio) fun _ =>
      ConfinedTo.bind_prog (hsl 0) fun _ => ConfinedTo.bind_prog (hsl 1) fun _ => hsl 2
  refine ConfinedTo.bind_prog (ConfinedTo.bind_prog hcp fun _ => ConfinedTo.pure_prog _)
    fun sPure => ?_
  unfold fbEnterFinishProg fbEnterFinishBodyProg fbFillTailOwnerLoopProg fbWriteModeOneProg
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  have hft : ∀ tl, ConfinedTo M
      (iterate fbFillTailOwnerStepProg (mctx0, sPure * k) tl 0) := fun tl => by
    refine ConfinedTo.iterate_prog _ (fun t => ?_) tl 0
    unfold fbFillTailOwnerStepProg fbFillTailOwnerWriteProg fbSlotBktRawProg fbSlotBktTag2Prog
    refine ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
      ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
    simp only [pure_bind]
    have hto : ∀ P off, ConfinedTo M (fbTailOwnerAtBlkProg (mctx0, (P, off))) := fun _ _ => by
      unfold fbTailOwnerAtBlkProg
      exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpTbSlotProg M _) fun _ =>
        confinedTo_bpReadTailOwnerProg hm
    refine ConfinedTo.bind_prog ?_ fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ => ConfinedTo.pure_prog _
    refine ConfinedTo.bind_prog (confinedTo_bpDivModKProg M _) fun dm' => ?_
    rcases dm' with ⟨P, off⟩
    refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => confinedTo_bpReadSlabOwnerProg hm) fun _ => ?_
    refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => hto P off)
    refine ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpActCurProg hm) fun _ => ?_
    exact ConfinedTo.ite_prog (fun _ => ConfinedTo.pure_prog _) (fun _ => hto P off)
  refine ConfinedTo.bind_prog (hft _) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteScalarProg hm) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => ConfinedTo.write_prog hm2 1) (fun _ => ConfinedTo.pure_prog _)

/-- `fallbackInsertProg` is confined to `M` under `FeistelConf`, `BpMetaConf`, and
`SlotIoDirectConf`. -/
theorem confinedTo_fallbackInsertProg {M : ℕ → Prop} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {u_val v_val : ℕ}
    (hf : FeistelConf M fctx) (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fallbackInsertProg (((fctx, (mctx, ioctx)), u_val), v_val)) := by
  rcases mctx with ⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩
  unfold fallbackInsertProg fbInsertNewProg fbInsertNewCheckProg fbInsertNewCommitProg
  refine ConfinedTo.bind_prog (confinedTo_feistelSplitBoundedProg hf) fun bq =>
    ConfinedTo.bind_prog (cf_fbScanProg hm hio) fun _ => ?_
  rcases bq with ⟨bkt, q_u⟩
  refine ConfinedTo.ite_prog (fun _ => confinedTo_slotIoWriteRawProg hio) fun _ => ?_
  refine ConfinedTo.bind_prog (cf_fbMaybePromoteProg hm hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpReadScalarProg hm) fun _ => ?_
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  refine ConfinedTo.ite_prog (fun _ => ?_) (fun _ => ConfinedTo.pure_prog _)
  simp only [pure_bind]
  exact ConfinedTo.bind_prog (confinedTo_slotIoAppendRawProg hio) fun _ =>
    ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ =>
    confinedTo_bpWriteScalarProg hm

/-- `fallbackDeleteProg` is confined to `M` under `FeistelConf`, `BpMetaConf`, and
`SlotIoDirectConf`. -/
theorem confinedTo_fallbackDeleteProg {M : ℕ → Prop} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {u_val : ℕ}
    (hf : FeistelConf M fctx) (hm : BpMetaConf M mctx) (hio : SlotIoDirectConf M ioctx) :
    ConfinedTo M (fallbackDeleteProg ((fctx, (mctx, ioctx)), u_val)) := by
  unfold fallbackDeleteProg
  refine ConfinedTo.bind_prog (confinedTo_feistelSplitBoundedProg hf) fun _ =>
    ConfinedTo.bind_prog (cf_fbScanProg hm hio) fun _ => ?_
  exact ConfinedTo.ite_prog (fun _ => cf_fbDeleteSlotProg hm hio) (fun _ => ConfinedTo.pure_prog _)

/-! ## Section 3: `SlotStateCoupled` (`io.sideBit = 0`) for Phase-`8` Source Draining -/

/-- State coupling between two memory states `s₁, s₂` sharing metadata region `M` (disjoint from
`io.OwnsAddr`) and virtual pair array `slotIoPairAt io · idx` (`idx < n`) on a source slot
(`io.sideBit = 0`). -/
structure SlotStateCoupled (M : ℕ → Prop) (io : SlotIoLayout) (n : ℕ)
    (s₁ s₂ : Memory.State) : Prop where
  /-- Equal hardware frontiers. -/
  fr_eq : s₁.frontier = s₂.frontier
  /-- Source-slot side bit is `0` (`io.side = false`). -/
  side_zero : io.sideBit = 0
  /-- `SlotIoLayout` validity on `s₁` (hence on `s₂` via `fr_eq`). -/
  valid₁ : io.Valid io.pgL.w s₁.frontier
  /-- Metadata region `M` is disjoint from `io.OwnsAddr`. -/
  disj : ∀ addr, M addr → io.OwnsAddr addr → False
  /-- Word-for-word memory agreement on `M`. -/
  mem_eq : ∀ addr, M addr → s₁.mem addr = s₂.mem addr
  /-- `io.StateInv n 0` on `s₁`. -/
  inv₁ : io.StateInv n 0 s₁.mem
  /-- `io.StateInv n 0` on `s₂`. -/
  inv₂ : io.StateInv n 0 s₂.mem
  /-- Virtual pair agreement across `[0, n)`. -/
  pair_eq : ∀ idx < n, slotIoPairAt io s₁.mem idx = slotIoPairAt io s₂.mem idx

/-- Step relation bundling equal `clientResult` with post-state `SlotStateCoupled M io n'`. -/
structure SlotCoupledStep {α : Type} (M : ℕ → Prop) (io : SlotIoLayout) (n' : ℕ)
    (s₁ s₂ : Memory.State) (p : Memory.Prog α) : Prop where
  /-- Equal return values. -/
  res_eq : (Memory.spec 0).clientResult s₁ p = (Memory.spec 0).clientResult s₂ p
  /-- Post-state coupling. -/
  coupled : SlotStateCoupled M io n'
    ((Memory.spec 0).clientState s₁ p) ((Memory.spec 0).clientState s₂ p)

namespace SlotStateCoupled

/-- `SlotIoLayout.Valid` on `s₂` follows immediately from `fr_eq`. -/
theorem valid₂ {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) : io.Valid io.pgL.w s₂.frontier :=
  hc.fr_eq ▸ hc.valid₁

/-- Rewrite the virtual slot count `n = n'`. -/
theorem cast_n {M : ℕ → Prop} {io : SlotIoLayout} {n n' : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (hn : n = n') :
    SlotStateCoupled M io n' s₁ s₂ :=
  hn ▸ hc

/-- Rewrite the first state `s₁ = s₁'` without unfolding `s₂`. -/
theorem cast_s₁ {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ} {s₁ s₁' s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (hs : s₁ = s₁') :
    SlotStateCoupled M io n s₁' s₂ :=
  hs ▸ hc

/-- When `io.sideBit = 0` and `io.StateInv n 0 mem`, `cleanPhase` is `0` whenever `io.usePaged ≠ 0`.
-/
private theorem cleanPhase_zero {io : SlotIoLayout} {n : ℕ} {mem : ℕ → ℕ}
    (hs : io.sideBit = 0) (hinv : io.StateInv n 0 mem) (hup : io.usePaged ≠ 0) :
    (extractPageUnperm io.pgL mem).cleanPhase = 0 := by
  unfold SlotIoLayout.StateInv at hinv
  rw [ite_eq_right hup] at hinv
  obtain ⟨_, _, _, _, _, hsd, _⟩ := hinv
  by_contra hne
  have htrue := hsd (Nat.pos_of_ne_zero hne)
  unfold SlotIoLayout.side at htrue
  simp [hs] at htrue

end SlotStateCoupled

namespace SlotCoupledStep

/-- `pure x` preserves `SlotStateCoupled M io n`. -/
theorem pure_prog {α : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (x : α) :
    SlotCoupledStep M io n s₁ s₂ (pure x) :=
  ⟨rfl, hc⟩

/-- Rewrite `n' = n''` in `SlotCoupledStep`. -/
theorem cast_n {α : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n' n'' : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α}
    (h : SlotCoupledStep M io n' s₁ s₂ p) (hn : n' = n'') :
    SlotCoupledStep M io n'' s₁ s₂ p :=
  hn ▸ h

/-- Monadic bind (`>>=`) composition for `SlotCoupledStep`. -/
theorem bind_prog {α β : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n₂ n₃ : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : SlotCoupledStep M io n₂ s₁ s₂ p)
    (hq : SlotStateCoupled M io n₂
        ((Memory.spec 0).clientState s₁ p) ((Memory.spec 0).clientState s₂ p) →
      SlotCoupledStep M io n₃
        ((Memory.spec 0).clientState s₁ p) ((Memory.spec 0).clientState s₂ p)
        (q ((Memory.spec 0).clientResult s₁ p))) :
    SlotCoupledStep M io n₃ s₁ s₂ (p >>= q) := by
  obtain ⟨hres_p, hc₂⟩ := hp
  obtain ⟨hres_q, hc₃⟩ := hq hc₂
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      ← hres_p, hres_q]
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, ← hres_p]
    exact hc₃

/-- Bind combinator for a read-only prefix on `s₁` (`clientState s₁ p = s₁`), avoiding `rw` on `s₂`.
-/
theorem bind_readOnly {α β : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n₂ n₃ : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : SlotCoupledStep M io n₂ s₁ s₂ p)
    (hst₁ : (Memory.spec 0).clientState s₁ p = s₁)
    (hq : SlotStateCoupled M io n₂ s₁ ((Memory.spec 0).clientState s₂ p) →
      SlotCoupledStep M io n₃ s₁ ((Memory.spec 0).clientState s₂ p)
        (q ((Memory.spec 0).clientResult s₁ p))) :
    SlotCoupledStep M io n₃ s₁ s₂ (p >>= q) := by
  obtain ⟨hres_p, hc₂⟩ := hp
  obtain ⟨hres_q, hc₃⟩ := hq (hc₂.cast_s₁ hst₁)
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hst₁,
      ← hres_p, hres_q]
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, hst₁,
      ← hres_p]
    exact hc₃

/-- Bind combinator for a read-only prefix on `s₁` with known return value `r₀` on `s₁`. -/
theorem bind_readOnly_eq {α β : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n₂ n₃ : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α} {r₀ : α} {q : α → Memory.Prog β}
    (hp : SlotCoupledStep M io n₂ s₁ s₂ p)
    (hst₁ : (Memory.spec 0).clientState s₁ p = s₁)
    (hres₁ : (Memory.spec 0).clientResult s₁ p = r₀)
    (hq : SlotStateCoupled M io n₂ s₁ ((Memory.spec 0).clientState s₂ p) →
      SlotCoupledStep M io n₃ s₁ ((Memory.spec 0).clientState s₂ p) (q r₀)) :
    SlotCoupledStep M io n₃ s₁ s₂ (p >>= q) := by
  obtain ⟨hres_p, hc₂⟩ := hp
  have hres₂ : (Memory.spec 0).clientResult s₂ p = r₀ := hres_p.symm.trans hres₁
  obtain ⟨hres_q, hc₃⟩ := hq (hc₂.cast_s₁ hst₁)
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind, hst₁,
      hres₁, hres₂, hres_q]
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, hst₁,
      hres₁, hres₂]
    exact hc₃

/-- Conditional (`if-then-else`) composition for `SlotCoupledStep`. -/
theorem ite_prog {α : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n' : ℕ}
    {s₁ s₂ : Memory.State} {P : Prop} [Decidable P] {p₁ p₂ : Memory.Prog α}
    (h₁ : P → SlotCoupledStep M io n' s₁ s₂ p₁)
    (h₂ : ¬P → SlotCoupledStep M io n' s₁ s₂ p₂) :
    SlotCoupledStep M io n' s₁ s₂ (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

/-- Fuel-indexed `iterate` combinator for `SlotCoupledStep` carrying a single-state invariant `P`.
-/
private theorem iterate_fuel {δ σ : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ}
    {body : δ × σ → Memory.Prog σ} (d : δ)
    (P : ℕ → σ → Memory.State → Prop)
    (hb : ∀ k a st₁ st₂, P (k + 1) a st₁ → SlotStateCoupled M io n st₁ st₂ →
      SlotCoupledStep M io n st₁ st₂ (body (d, a)) ∧
      P k ((Memory.spec 0).clientResult st₁ (body (d, a)))
        ((Memory.spec 0).clientState st₁ (body (d, a)))) :
    ∀ fuel a₀ s₁ s₂, P fuel a₀ s₁ → SlotStateCoupled M io n s₁ s₂ →
      SlotCoupledStep M io n s₁ s₂ (iterate body d fuel a₀) ∧
      P 0 ((Memory.spec 0).clientResult s₁ (iterate body d fuel a₀))
        ((Memory.spec 0).clientState s₁ (iterate body d fuel a₀)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a₀ _ _ hP hc
    exact ⟨pure_prog hc a₀, hP⟩
  | succ k ih =>
    intro a₀ s₁ s₂ hP hc
    unfold iterate
    obtain ⟨hstep, hPk⟩ := hb k a₀ s₁ s₂ hP hc
    refine ⟨bind_prog hstep fun hc' => (ih _ _ _ hPk hc').1, ?_⟩
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
    exact (ih _ _ _ hPk hstep.coupled).2

/-- Any `ConfinedTo M p` preserves `SlotStateCoupled M io n` with equal return value. -/
theorem of_confinedTo {α : Type} {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ}
    {s₁ s₂ : Memory.State} {p : Memory.Prog α}
    (hc : SlotStateCoupled M io n s₁ s₂) (hp : ConfinedTo M p) :
    SlotCoupledStep M io n s₁ s₂ p := by
  have hw := hc.valid₁.w_pos
  have hout₁ : ∀ addr, io.OwnsAddr addr →
      ((Memory.spec 0).clientState s₁ p).mem addr = s₁.mem addr :=
    fun addr hia => hp.mem_out s₁ addr (fun hm => hc.disj addr hm hia)
  have hout₂ : ∀ addr, io.OwnsAddr addr →
      ((Memory.spec 0).clientState s₂ p).mem addr = s₂.mem addr :=
    fun addr hia => hp.mem_out s₂ addr (fun hm => hc.disj addr hm hia)
  obtain ⟨hinv₁', harr₁'⟩ := io.congr_of_outside hw hc.inv₁ hout₁
  obtain ⟨hinv₂', harr₂'⟩ := io.congr_of_outside hw hc.inv₂ hout₂
  refine ⟨hp.res_eq s₁ s₂ hc.mem_eq, {
    fr_eq := (hp.fr_eq s₁).trans (hc.fr_eq.trans (hp.fr_eq s₂).symm)
    side_zero := hc.side_zero
    valid₁ := (hp.fr_eq s₁).symm ▸ hc.valid₁
    disj := hc.disj
    mem_eq := hp.mem_in s₁ s₂ hc.mem_eq
    inv₁ := hinv₁'
    inv₂ := hinv₂'
    pair_eq := fun idx hidx =>
      (harr₁' idx hidx).trans ((hc.pair_eq idx hidx).trans (harr₂' idx hidx).symm)
  }⟩

/-- `slotIoReadRawProg` at `idx < n` returns equal pairs and preserves `SlotStateCoupled`. -/
private theorem slotIoRead {M : ℕ → Prop} {io : SlotIoLayout} {n idx : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (hidx : idx < n) :
    SlotCoupledStep M io n s₁ s₂ (slotIoReadRawProg (io.toCtx, idx)) := by
  obtain ⟨hr₁, hs₁⟩ := slotIoReadProg_spec hc.inv₁ hidx
  obtain ⟨hr₂, hs₂⟩ := slotIoReadProg_spec hc.inv₂ hidx
  unfold slotIoReadProg at hr₁ hs₁ hr₂ hs₂
  refine ⟨hr₁.trans ((hc.pair_eq idx hidx).trans hr₂.symm), ?_⟩
  rw [hs₁, hs₂]
  exact hc

/-- `slotIoWriteRawProg` at `idx < n` preserves `SlotStateCoupled M io n`. -/
private theorem slotIoWrite {M : ℕ → Prop} {io : SlotIoLayout} {n idx q v : ℕ}
    {s₁ s₂ : Memory.State} (hc : SlotStateCoupled M io n s₁ s₂) (hidx : idx < n)
    (hq : q < 2 ^ io.pgL.qBits) (hv : v < 2 ^ io.pgL.vBits) :
    SlotCoupledStep M io n s₁ s₂ (slotIoWriteRawProg ((io.toCtx, idx), (q, v))) := by
  have hwf := slotIoWriteProg_frame hc.valid₁.w_pos idx q v
  obtain ⟨hinv₁', harr₁', _⟩ := slotIoWriteProg_spec hc.valid₁ hc.inv₁ hidx hq hv
  obtain ⟨hinv₂', harr₂', _⟩ := slotIoWriteProg_spec hc.valid₂ hc.inv₂ hidx hq hv
  unfold slotIoWriteProg at hwf hinv₁' harr₁' hinv₂' harr₂'
  exact ⟨Subsingleton.elim _ _, {
    fr_eq := (hwf.frontier_eq s₁).trans (hc.fr_eq.trans (hwf.frontier_eq s₂).symm)
    side_zero := hc.side_zero
    valid₁ := (hwf.frontier_eq s₁).symm ▸ hc.valid₁
    disj := hc.disj
    mem_eq := fun addr hm =>
      (hwf.mem_outside s₁ addr (hc.disj addr hm)).trans
        ((hc.mem_eq addr hm).trans (hwf.mem_outside s₂ addr (hc.disj addr hm)).symm)
    inv₁ := hinv₁'
    inv₂ := hinv₂'
    pair_eq := fun idx₂ hidx₂ => by
      rw [harr₁' idx₂ hidx₂, harr₂' idx₂ hidx₂]
      by_cases he : idx₂ = idx
      · rw [ite_eq_left he, ite_eq_left he]
      · rw [ite_eq_right he, ite_eq_right he, hc.pair_eq idx₂ hidx₂]
  }⟩

/-- `slotIoSwapRawProg` at `p₁ < n, p₂ < n` preserves `SlotStateCoupled M io n`. -/
private theorem slotIoSwap {M : ℕ → Prop} {io : SlotIoLayout} {n p₁ p₂ : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (hp₁ : p₁ < n) (hp₂ : p₂ < n) :
    SlotCoupledStep M io n s₁ s₂ (slotIoSwapRawProg (io.toCtx, (p₁, p₂))) := by
  unfold slotIoSwapRawProg
  refine ite_prog (fun _ => pure_prog hc ()) fun _ => ?_
  refine bind_prog (slotIoRead hc hp₁) fun hc1 => ?_
  refine bind_prog (slotIoRead hc1 hp₂) fun hc2 => ?_
  obtain ⟨hr1, hs1⟩ := slotIoReadProg_spec hc.inv₁ hp₁
  unfold slotIoReadProg at hr1 hs1
  have hr2 : (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s₁ (slotIoReadRawProg (io.toCtx, p₁)))
      (slotIoReadRawProg (io.toCtx, p₂)) = slotIoPairAt io s₁.mem p₂ := by
    rw [hs1]
    exact (slotIoReadProg_spec hc.inv₁ hp₂).1
  rw [hr2, hr1]
  obtain ⟨hq₁, hv₁⟩ := slotIoPairAt_bounds (io := io) s₁.mem p₁
  obtain ⟨hq₂, hv₂⟩ := slotIoPairAt_bounds (io := io) s₁.mem p₂
  exact bind_prog (slotIoWrite hc2 hp₁ hq₂ hv₂) fun hc3 => slotIoWrite hc3 hp₂ hq₁ hv₁

/-- `slotIoPopBackRawProg` (`0 < n`) transitions `SlotStateCoupled M io n` to `n - 1`. -/
theorem slotIoPopBack {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (hpos : 0 < n) :
    SlotCoupledStep M io (n - 1) s₁ s₂ (slotIoPopBackRawProg io.toCtx) := by
  have hwf := slotIoPopBackProg_frame hc.valid₁.w_pos
  obtain ⟨hinv₁', harr₁', _⟩ := slotIoPopBackProg_spec hc.valid₁ hc.inv₁ hpos
  obtain ⟨hinv₂', harr₂', _⟩ := slotIoPopBackProg_spec hc.valid₂ hc.inv₂ hpos
  unfold slotIoPopBackProg at hwf hinv₁' harr₁' hinv₂' harr₂'
  have hsl₁ : (if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s₁.mem).cleanPhase = 0 then 0
      else 24) = 0 := by
    by_cases h0 : io.usePaged = 0
    · simp [h0]
    · simp [h0, SlotStateCoupled.cleanPhase_zero hc.side_zero hc.inv₁ h0]
  have hsl₂ : (if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s₂.mem).cleanPhase = 0 then 0
      else 24) = 0 := by
    by_cases h0 : io.usePaged = 0
    · simp [h0]
    · simp [h0, SlotStateCoupled.cleanPhase_zero hc.side_zero hc.inv₂ h0]
  rw [hsl₁] at hinv₁'
  rw [hsl₂] at hinv₂'
  exact ⟨Subsingleton.elim _ _, {
    fr_eq := (hwf.frontier_eq s₁).trans (hc.fr_eq.trans (hwf.frontier_eq s₂).symm)
    side_zero := hc.side_zero
    valid₁ := (hwf.frontier_eq s₁).symm ▸ hc.valid₁
    disj := hc.disj
    mem_eq := fun addr hm =>
      (hwf.mem_outside s₁ addr (hc.disj addr hm)).trans
        ((hc.mem_eq addr hm).trans (hwf.mem_outside s₂ addr (hc.disj addr hm)).symm)
    inv₁ := hinv₁'
    inv₂ := hinv₂'
    pair_eq := fun idx hidx =>
      (harr₁' idx hidx).trans ((hc.pair_eq idx (by omega)).trans (harr₂' idx hidx).symm)
  }⟩

end SlotCoupledStep

/-! ## Section 4: `SlotCoupledStep` for `SmallRegime`, `LargeBlockPool`, and `FallbackPool` -/

private theorem smallEpochScanRaw_coupled {M : ℕ → Prop} {io : SlotIoLayout}
    {mb n u_key : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (h0 : M mb) (h1 : M (mb + 1))
    (hns : s₁.mem (mb + 1) = n) :
    SlotCoupledStep M io n s₁ s₂ (smallEpochScanRawProg ((io.toCtx, mb), u_key)) ∧
    ((Memory.spec 0).clientState s₁ (smallEpochScanRawProg ((io.toCtx, mb), u_key)) = s₁) ∧
    (((Memory.spec 0).clientResult s₁ (smallEpochScanRawProg ((io.toCtx, mb), u_key))).1 = 1 →
      ((Memory.spec 0).clientResult s₁
        (smallEpochScanRawProg ((io.toCtx, mb), u_key))).2.1 < n) := by
  have hloop := SlotCoupledStep.iterate_fuel
    (M := M) (io := io) (n := n) (body := smallEpochScanStepProg)
    (io.toCtx, (mb, (n, u_key)))
    (fun _ acc st => st = s₁ ∧ (acc.1.2 = 1 → acc.2.1 < n))
    (fun _ ⟨⟨cur, found⟩, ⟨hitIdx, hitVal⟩⟩ st₁ st₂ ⟨hst_eq, hhit⟩ hc_st => by
      subst st₁
      unfold smallEpochScanStepProg
      have hcs : SlotCoupledStep M io n s₁ st₂
          (do
            let _ ← Memory.read mb
            if cur < n then do
              let qv ← slotIoReadRawProg (io.toCtx, cur)
              if found = 0 ∧ qv.1 = u_key then pure ((cur + 1, 1), (cur, qv.2))
              else pure ((cur + 1, found), (hitIdx, hitVal))
            else pure ((cur, found), (hitIdx, hitVal))) :=
        SlotCoupledStep.bind_prog (SlotCoupledStep.of_confinedTo hc_st (ConfinedTo.read_prog h0))
          fun hc_a => SlotCoupledStep.ite_prog
            (fun hlt => SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoRead hc_a hlt)
              fun hc_b => SlotCoupledStep.ite_prog
                (fun _ => SlotCoupledStep.pure_prog hc_b _)
                (fun _ => SlotCoupledStep.pure_prog hc_b _))
            (fun _ => SlotCoupledStep.pure_prog hc_a _)
      refine ⟨hcs, ?_⟩
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s₁ (Memory.read mb) = s₁ from rfl]
      by_cases hlt : cur < n
      · obtain ⟨_, hr_st⟩ := slotIoReadProg_spec hc_st.inv₁ hlt
        unfold slotIoReadProg at hr_st
        rw [ite_eq_left hlt, StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientState_bind, hr_st]
        rcases (Memory.spec 0).clientResult s₁ (slotIoReadRawProg (io.toCtx, cur)) with ⟨q, v⟩
        dsimp only
        by_cases hm : found = 0 ∧ q = u_key
        · rw [ite_eq_left hm]; exact ⟨rfl, fun _ => hlt⟩
        · rw [ite_eq_right hm]; exact ⟨rfl, hhit⟩
      · rw [ite_eq_right hlt]; exact ⟨rfl, hhit⟩)
    n ((0, 0), (0, 0)) s₁ s₂ ⟨rfl, fun h => absurd h (by decide)⟩ hc
  unfold smallEpochScanRawProg smallEpochScanLoopProg
  have hrd_res : (Memory.spec 0).clientResult s₁ (Memory.read (mb + 1)) = n := hns
  have hrd_st : (Memory.spec 0).clientState s₁ (Memory.read (mb + 1)) = s₁ := rfl
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    refine SlotCoupledStep.bind_prog
      (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog h1)) fun hc1 => ?_
    rw [hrd_st] at hc1 ⊢
    rw [hrd_res]
    refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc1 _)
    simp only [pure_bind]
    exact SlotCoupledStep.bind_prog hloop.1 fun hc2 => SlotCoupledStep.pure_prog hc2 _
  · dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [StateTransitionSpec.clientState_bind, hrd_st, hrd_res]
    split_ifs
    · simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
      exact (show (Memory.spec 0).clientState s₁ (iterate smallEpochScanStepProg
        (io.toCtx, (mb, (n, u_key))) n ((0, 0), (0, 0))) = s₁ from hloop.2.1)
    · rfl
  · conv_lhs => dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    conv_rhs => dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    simp only [StateTransitionSpec.clientResult_bind, hrd_st, hrd_res]
    by_cases hle : n ≤ io.pgL.nCap
    · simp only [ite_eq_left hle, pure_bind, StateTransitionSpec.clientResult_bind]
      have hst_loop : (Memory.spec 0).clientState s₁
          (iterate smallEpochScanStepProg (io.toCtx, (mb, (n, u_key))) n ((0, 0), (0, 0))) = s₁ :=
        hloop.2.1
      dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx] at hst_loop
      rw [hst_loop]
      exact hloop.2.2
    · simp only [ite_eq_right hle]; rintro ⟨⟩

/-- `smallEpochDeleteRawProg` preserves `SlotStateCoupled` (`n' = s₁'.mem (mb + 1)`). -/
theorem smallEpochDeleteRaw_coupled {M : ℕ → Prop} {io : SlotIoLayout}
    {mb n u_key : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (h0 : M mb) (h1 : M (mb + 1))
    (hns : s₁.mem (mb + 1) = n) :
    let s₁' := (Memory.spec 0).clientState s₁ (smallEpochDeleteRawProg ((io.toCtx, mb), u_key))
    SlotCoupledStep M io (s₁'.mem (mb + 1)) s₁ s₂
      (smallEpochDeleteRawProg ((io.toCtx, mb), u_key)) := by
  dsimp only
  obtain ⟨hscan_cs, hscan_st, hscan_lt⟩ := smallEpochScanRaw_coupled hc h0 h1 hns
  rcases hr : (Memory.spec 0).clientResult s₁ (smallEpochScanRawProg ((io.toCtx, mb), u_key)) with
    ⟨f, ⟨hitIdx, hitVal⟩⟩
  rw [hr] at hscan_lt
  have hrd : (Memory.spec 0).clientResult s₁ (Memory.read (mb + 1)) = n := hns
  by_cases hf1 : f = 1
  · have hidx_lt : hitIdx < n := hscan_lt hf1
    have hpos : 0 < n := by omega
    have hs1_end : ((Memory.spec 0).clientState s₁
        (smallEpochDeleteRawProg ((io.toCtx, mb), u_key))).mem (mb + 1) = n - 1 := by
      unfold smallEpochDeleteRawProg
      rw [StateTransitionSpec.clientState_bind, hscan_st, hr]; dsimp only
      rw [ite_eq_left hf1, StateTransitionSpec.clientState_bind]
      change ((Memory.spec 0).clientState s₁ _).mem (mb + 1) = n - 1
      rw [hrd, ite_eq_left hpos]; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      change Function.update (_ : ℕ → ℕ) (mb + 1) (n - 1) (mb + 1) = n - 1
      exact Function.update_self ..
    refine (?_ : SlotCoupledStep M io (n - 1) s₁ s₂
      (smallEpochDeleteRawProg ((io.toCtx, mb), u_key))).cast_n hs1_end.symm
    unfold smallEpochDeleteRawProg
    refine SlotCoupledStep.bind_readOnly_eq hscan_cs hscan_st hr fun hc1 => ?_
    dsimp only; rw [ite_eq_left hf1]
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc1 (ConfinedTo.read_prog h1)) rfl hrd fun hc2 => ?_
    rw [ite_eq_left hpos]; simp only [pure_bind]
    exact SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoSwap hc2 hidx_lt (by omega))
      fun hc3 => SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoPopBack hc3 hpos)
      fun hc4 => SlotCoupledStep.of_confinedTo hc4 (ConfinedTo.write_prog h1 (n - 1))
  · have hs1_end : ((Memory.spec 0).clientState s₁
        (smallEpochDeleteRawProg ((io.toCtx, mb), u_key))).mem (mb + 1) = n := by
      unfold smallEpochDeleteRawProg
      rw [StateTransitionSpec.clientState_bind, hscan_st, hr]; dsimp only
      rw [ite_eq_right hf1]; exact hns
    refine (?_ : SlotCoupledStep M io n s₁ s₂
      (smallEpochDeleteRawProg ((io.toCtx, mb), u_key))).cast_n hs1_end.symm
    unfold smallEpochDeleteRawProg
    refine SlotCoupledStep.bind_readOnly_eq hscan_cs hscan_st hr fun hc1 => ?_
    dsimp only; rw [ite_eq_right hf1]
    exact SlotCoupledStep.pure_prog hc1 ()

/-- `smallEpochPopAnyRawProg` (`0 < n`) pops the identical `(u, v)` pair and transitions
`SlotStateCoupled M io n` to `n - 1`. -/
theorem smallEpochPopAnyRaw_coupled {M : ℕ → Prop} {io : SlotIoLayout}
    {mb n : ℕ} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂) (h1 : M (mb + 1))
    (hns : s₁.mem (mb + 1) = n) (hpos : 0 < n) :
    SlotCoupledStep M io (n - 1) s₁ s₂ (smallEpochPopAnyRawProg (io.toCtx, mb)) := by
  unfold smallEpochPopAnyRawProg
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog h1)) fun hc1 => ?_
  have hrd_res : (Memory.spec 0).clientResult s₁ (Memory.read (mb + 1)) = n := hns
  rw [hrd_res, ite_eq_left hpos]; simp only [pure_bind]
  exact SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoRead hc1 (by omega)) fun hc2 =>
    SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoPopBack hc2 hpos) fun hc3 =>
    SlotCoupledStep.bind_prog
      (SlotCoupledStep.of_confinedTo hc3 (ConfinedTo.write_prog h1 (n - 1)))
      fun hc4 => SlotCoupledStep.pure_prog hc4 _

private theorem bpExecOptSwap_coupled {M : ℕ → Prop} {io : SlotIoLayout} {n : ℕ}
    {osw : Option PhysSwap} {s₁ s₂ : Memory.State}
    (hc : SlotStateCoupled M io n s₁ s₂)
    (hsw : ∀ sw, osw = some sw → sw.p₁ < n ∧ sw.p₂ < n) :
    SlotCoupledStep M io n s₁ s₂ (bpExecOptSwapProg (io.toCtx, encodeOptSwap osw)) := by
  cases osw with
  | none =>
    unfold encodeOptSwap bpExecOptSwapProg; dsimp only
    rw [ite_eq_left rfl]
    exact SlotCoupledStep.pure_prog hc ()
  | some sw =>
    obtain ⟨hp₁, hp₂⟩ := hsw sw rfl
    unfold encodeOptSwap bpExecOptSwapProg; dsimp only
    rw [ite_eq_right Nat.one_ne_zero]
    exact SlotCoupledStep.slotIoSwap hc hp₁ hp₂

private theorem bpBktTickStep_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b t : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hsi : (extractBlockPool bpL.mp s₁.mem).StepInv b t)
    (hb : b < bpL.mp.M)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpBktTickStepProg (bpL.toCtx, b)) := by
  have hstep := hsi.bktTickOne_spec.{0} hb
  rcases hbt_one : (extractBlockPool bpL.mp s₁.mem).bktTickOne b with ⟨bp_next, osw_next⟩
  rw [hbt_one] at hstep
  obtain ⟨_, _, _, _, _, _, hsw_lt, _⟩ := hstep
  have hbt := bpBktTickMetaProg_spec hv.mp_valid hsi.core hb hn_le (hsi.bktCount_le b hb)
  dsimp only at hbt; rw [hbt_one] at hbt
  unfold bpBktTickStepProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpBktTickMetaProg hm)) fun hc1 => ?_
  rw [hbt.2]
  exact bpExecOptSwap_coupled hc1 hsw_lt

private theorem bpRunBktTicks16_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b t : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hsi : (extractBlockPool bpL.mp s₁.mem).StepInv b t)
    (hb : b < bpL.mp.M)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpRunBktTicks16Prog (bpL.toCtx, b)) := by
  have comp : ∀ {k : ℕ} {p : BlockPoolCtx × ℕ → Memory.Prog Unit},
      (∀ t' sA sB, bpL.Valid bpL.mp.w sA.frontier →
        (extractBlockPool bpL.mp sA.mem).StepInv b t' →
        (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
        SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
        SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB (p (bpL.toCtx, b)) ∧
        let sA' := (Memory.spec 0).clientState sA (p (bpL.toCtx, b))
        sA'.frontier = sA.frontier ∧
        (extractBlockPool bpL.mp sA'.mem).StepInv b (t' - k) ∧
        (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide) →
      ∀ t' sA sB, bpL.Valid bpL.mp.w sA.frontier →
        (extractBlockPool bpL.mp sA.mem).StepInv b t' →
        (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
        SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
        SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB
          (p (bpL.toCtx, b) >>= fun _ => p (bpL.toCtx, b)) ∧
        let sA' := (Memory.spec 0).clientState sA (p (bpL.toCtx, b) >>= fun _ => p (bpL.toCtx, b))
        sA'.frontier = sA.frontier ∧
        (extractBlockPool bpL.mp sA'.mem).StepInv b (t' - (k + k)) ∧
        (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide := by
    intro k p hp t' sA sB hvA hsiA hnA hcA
    obtain ⟨hcs1, hfr1, hsi1, hn1⟩ := hp t' sA sB hvA hsiA hnA hcA
    set sA₁ := (Memory.spec 0).clientState sA (p (bpL.toCtx, b))
    set sB₁ := (Memory.spec 0).clientState sB (p (bpL.toCtx, b))
    obtain ⟨hcs2, hfr2, hsi2, hn2⟩ :=
      hp (t' - k) sA₁ sB₁ (hfr1.symm ▸ hvA) hsi1 (hn1 ▸ hnA) (hn1.symm ▸ hcs1.coupled)
    refine ⟨SlotCoupledStep.bind_prog hcs1 fun _ => hn1 ▸ hcs2, ?_⟩
    rw [StateTransitionSpec.clientState_bind]
    exact ⟨hfr2.trans hfr1, Nat.sub_sub t' k k ▸ hsi2, hn2.trans hn1⟩
  have h1 : ∀ t' sA sB, bpL.Valid bpL.mp.w sA.frontier →
      (extractBlockPool bpL.mp sA.mem).StepInv b t' →
      (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
      SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
      SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB
        (bpBktTickStepProg (bpL.toCtx, b)) ∧
      let sA' := (Memory.spec 0).clientState sA (bpBktTickStepProg (bpL.toCtx, b))
      sA'.frontier = sA.frontier ∧
      (extractBlockPool bpL.mp sA'.mem).StepInv b (t' - 1) ∧
      (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide := by
    intro t' sA sB hvA hsiA hnA hcA
    obtain ⟨hfr, hex, hsi', hn', _, _, _⟩ := bpBktTickStepProg_spec hvA hsiA hb hnA hcA.inv₁
    exact ⟨bpBktTickStep_coupled hvA hm hsiA hb hnA hcA, hfr, hex ▸ hsi', hex ▸ hn'⟩
  exact (comp (comp (comp (comp h1))) t s₁ s₂ hv hsi hn_le hc).1

private theorem bpTopCleanStep_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b₀ : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hsi : (extractBlockPool bpL.mp s₁.mem).StepInv b₀ 0)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpTopCleanStepProg bpL.toCtx) := by
  have hstep := hsi.topCleanOne_debt_spec.{0}
  rcases htc_one : (extractBlockPool bpL.mp s₁.mem).topCleanOne with ⟨bp_next, osw_next⟩
  rw [htc_one] at hstep
  obtain ⟨_, _, _, _, _, _, hsw_lt, _⟩ := hstep
  have htc := bpTopCleanMetaProg_spec hv.mp_valid hsi.core hn_le hsi.bktCount_le
  dsimp only at htc; rw [htc_one] at htc
  unfold bpTopCleanStepProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpTopCleanMetaProg hm)) fun hc1 => ?_
  rw [htc.2]
  exact bpExecOptSwap_coupled hc1 hsw_lt

private theorem bpRunTopClean16_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b₀ : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hsi : (extractBlockPool bpL.mp s₁.mem).StepInv b₀ 0)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpRunTopClean16Prog bpL.toCtx) := by
  have comp : ∀ {p : BlockPoolCtx → Memory.Prog Unit},
      (∀ sA sB, bpL.Valid bpL.mp.w sA.frontier →
        (extractBlockPool bpL.mp sA.mem).StepInv b₀ 0 →
        (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
        SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
        SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB (p bpL.toCtx) ∧
        let sA' := (Memory.spec 0).clientState sA (p bpL.toCtx)
        sA'.frontier = sA.frontier ∧
        (extractBlockPool bpL.mp sA'.mem).StepInv b₀ 0 ∧
        (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide) →
      ∀ sA sB, bpL.Valid bpL.mp.w sA.frontier →
        (extractBlockPool bpL.mp sA.mem).StepInv b₀ 0 →
        (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
        SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
        SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB
          (p bpL.toCtx >>= fun _ => p bpL.toCtx) ∧
        let sA' := (Memory.spec 0).clientState sA (p bpL.toCtx >>= fun _ => p bpL.toCtx)
        sA'.frontier = sA.frontier ∧
        (extractBlockPool bpL.mp sA'.mem).StepInv b₀ 0 ∧
        (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide := by
    intro p hp sA sB hvA hsiA hnA hcA
    obtain ⟨hcs1, hfr1, hsi1, hn1⟩ := hp sA sB hvA hsiA hnA hcA
    set sA₁ := (Memory.spec 0).clientState sA (p bpL.toCtx)
    set sB₁ := (Memory.spec 0).clientState sB (p bpL.toCtx)
    obtain ⟨hcs2, hfr2, hsi2, hn2⟩ :=
      hp sA₁ sB₁ (hfr1.symm ▸ hvA) hsi1 (hn1 ▸ hnA) (hn1.symm ▸ hcs1.coupled)
    refine ⟨SlotCoupledStep.bind_prog hcs1 fun _ => hn1 ▸ hcs2, ?_⟩
    rw [StateTransitionSpec.clientState_bind]
    exact ⟨hfr2.trans hfr1, hsi2, hn2.trans hn1⟩
  have h1 : ∀ sA sB, bpL.Valid bpL.mp.w sA.frontier →
      (extractBlockPool bpL.mp sA.mem).StepInv b₀ 0 →
      (extractBlockPool bpL.mp sA.mem).nSide ≤ bpL.mp.nCap →
      SlotStateCoupled M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB →
      SlotCoupledStep M bpL.io (extractBlockPool bpL.mp sA.mem).nSide sA sB
        (bpTopCleanStepProg bpL.toCtx) ∧
      let sA' := (Memory.spec 0).clientState sA (bpTopCleanStepProg bpL.toCtx)
      sA'.frontier = sA.frontier ∧
      (extractBlockPool bpL.mp sA'.mem).StepInv b₀ 0 ∧
      (extractBlockPool bpL.mp sA'.mem).nSide = (extractBlockPool bpL.mp sA.mem).nSide := by
    intro sA sB hvA hsiA hnA hcA
    obtain ⟨hfr, hex, hsi', hn', _, _, _⟩ := bpTopCleanStepProg_spec hvA hsiA hnA hcA.inv₁
    exact ⟨bpTopCleanStep_coupled hvA hm hsiA hnA hcA, hfr, hex ▸ hsi', hex ▸ hn'⟩
  exact (comp (comp (comp (comp h1))) s₁ s₂ hv hsi hn_le hc).1

/-- `bpReadAtRawProg` at valid `(b, loc)` returns equal pairs and preserves `SlotStateCoupled`. -/
theorem bpReadAtRaw_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b loc : ℕ}
    {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hcv : (extractBlockPool bpL.mp s₁.mem).CoreValid)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hb : b < bpL.mp.M) (hloc : loc < (extractBlockPool bpL.mp s₁.mem).bktCount b)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpReadAtRawProg (bpL.toCtx, (b, loc))) := by
  unfold bpReadAtRawProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpToPhysProg hm)) fun hc1 => ?_
  rw [bpToPhysProg_spec hcv hn_le hb hloc]
  exact SlotCoupledStep.slotIoRead hc1 (hcv.toPhys_lt hb hloc)

/-- `bpWriteAtRawProg` at valid `(b, loc)` preserves `SlotStateCoupled`. -/
theorem bpWriteAtRaw_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b loc q v : ℕ}
    {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hcv : (extractBlockPool bpL.mp s₁.mem).CoreValid)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hb : b < bpL.mp.M) (hloc : loc < (extractBlockPool bpL.mp s₁.mem).bktCount b)
    (hq : q < 2 ^ bpL.io.pgL.qBits) (hv : v < 2 ^ bpL.io.pgL.vBits)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂
      (bpWriteAtRawProg ((bpL.toCtx, (b, loc)), (q, v))) := by
  unfold bpWriteAtRawProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpToPhysProg hm)) fun hc1 => ?_
  rw [bpToPhysProg_spec hcv hn_le hb hloc]
  exact SlotCoupledStep.slotIoWrite hc1 (hcv.toPhys_lt hb hloc) hq hv

private theorem bpPopBktPrepAndShrink_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hbal : (extractBlockPool bpL.mp s₁.mem).Balanced)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hb : b < bpL.mp.M) (hcnt : 0 < (extractBlockPool bpL.mp s₁.mem).bktCount b)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    let bp₀ := extractBlockPool bpL.mp s₁.mem
    let s₁' := (Memory.spec 0).clientState s₁ (bpPopBktPrepAndShrinkProg (bpL.toCtx, b))
    SlotCoupledStep M bpL.io (bp₀.nSide - 1) s₁ s₂
      (bpPopBktPrepAndShrinkProg (bpL.toCtx, b)) ∧
    s₁'.frontier = s₁.frontier ∧
    (extractBlockPool bpL.mp s₁'.mem).StepInv b 16 ∧
    (extractBlockPool bpL.mp s₁'.mem).nSide = bp₀.nSide - 1 := by
  dsimp only
  set bp₀ := extractBlockPool bpL.mp s₁.mem
  have hvIo : bpL.io.Valid bpL.io.pgL.w s₁.frontier := hv.w_eq_io ▸ hv.io_valid
  have hprep_pure := hbal.prepPopBktBack_spec.{0} hb hcnt
  dsimp only at hprep_pure
  set bp₁ := (bp₀.prepPopBktBack b).1
  set osw := (bp₀.prepPopBktBack b).2
  obtain ⟨hbal₁, hM₁, _, hn₁, hbc₁, hn_pos, htp_end, hsw_lt, _⟩ := hprep_pure
  have hpp_spec := bpPrepPopMetaProg_spec hv.mp_valid hbal hb hcnt hn_le
  dsimp only at hpp_spec
  obtain ⟨hex₁, hres₁⟩ := hpp_spec
  have hfr₁ : ((Memory.spec 0).clientState s₁ (bpPrepPopMetaProg (bpL.mp.toCtx, b))).frontier =
      s₁.frontier := runClient_frontier_bpPrepPopMetaProg (bpL.mp.toCtx, b) s₁
  obtain ⟨hio₁, _, _⟩ := meta_preserves_io hv (bpPrepPopMetaProg_frame hv.mp_valid b) hc.inv₁
  generalize hstA₁ : (Memory.spec 0).clientState s₁ (bpPrepPopMetaProg (bpL.mp.toCtx, b)) = stA₁
    at hex₁ hfr₁ hio₁
  have hfr₂ : ((Memory.spec 0).clientState stA₁
      (bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw))).frontier = s₁.frontier :=
    (frontier_bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw) stA₁
      (by simpa using hvIo.w_pos)).trans hfr₁
  have hv₁ : bpL.Valid bpL.mp.w stA₁.frontier := by rw [hfr₁]; exact hv
  obtain ⟨hex₂_rel, _, _, _⟩ := bpExecOptSwapProg_spec hv₁ hio₁ hsw_lt
  generalize hstA₂ :
    (Memory.spec 0).clientState stA₁ (bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw)) = stA₂
    at hfr₂ hex₂_rel
  have hex₂ : extractBlockPool bpL.mp stA₂.mem = bp₁ := hex₂_rel.trans hex₁
  have hfr₃ : ((Memory.spec 0).clientState stA₂ (slotIoPopBackRawProg bpL.io.toCtx)).frontier =
      s₁.frontier := (frontier_slotIoPopBackRawProg bpL.io.toCtx stA₂ hvIo.w_pos).trans hfr₂
  have hv₂ : bpL.Valid bpL.mp.w stA₂.frontier := by rw [hfr₂]; exact hv
  have hex₃_rel : extractBlockPool bpL.mp
      ((Memory.spec 0).clientState stA₂ (slotIoPopBackRawProg bpL.io.toCtx)).mem =
      extractBlockPool bpL.mp stA₂.mem := by
    have h := io_preserves_meta stA₂ hv₂ (slotIoPopBackProg_frame hvIo.w_pos)
    unfold slotIoPopBackProg at h; exact h
  generalize hstA₃ : (Memory.spec 0).clientState stA₂ (slotIoPopBackRawProg bpL.io.toCtx) = stA₃
    at hfr₃ hex₃_rel
  have hex₃ : extractBlockPool bpL.mp stA₃.mem = bp₁ := hex₃_rel.trans hex₂
  have hfr₄ : ((Memory.spec 0).clientState stA₃ (bpCommitPopMetaProg (bpL.mp.toCtx, b))).frontier =
      s₁.frontier := (runClient_frontier_bpCommitPopMetaProg (bpL.mp.toCtx, b) stA₃).trans hfr₃
  have hmv₃ : bpL.mp.Valid bpL.mp.w stA₃.frontier := by rw [hfr₃]; exact hv.mp_valid
  have hbal₃ : (extractBlockPool bpL.mp stA₃.mem).Balanced := by rw [hex₃]; exact hbal₁
  have hex₄_raw : extractBlockPool bpL.mp
      ((Memory.spec 0).clientState stA₃ (bpCommitPopMetaProg (bpL.mp.toCtx, b))).mem =
      bp₁.commitPopBktBack b := by
    have h := bpCommitPopMetaProg_spec hmv₃ hbal₃ hb
      (by rw [hex₃, hn₁]; exact hn_pos) (by rw [hex₃, hn₁]; exact hn_le)
    rwa [hex₃] at h
  generalize hstA₄ : (Memory.spec 0).clientState stA₃ (bpCommitPopMetaProg (bpL.mp.toCtx, b)) =
    stA₄ at hfr₄ hex₄_raw
  have htp_end₁ : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1 := by rwa [hbc₁ b, hn₁]
  have hb₁ : b < bp₁.M := by rw [hM₁]; exact hb
  have hpos₁ : 0 < bp₁.nSide := by rw [hn₁]; exact hn_pos
  obtain ⟨hsi₄, _, _, hn_cp, _, _, _, _⟩ :=
    hbal₁.commitPopBktBack_spec hb₁ (by rwa [hbc₁ b]) hpos₁ htp_end₁
  have hns_s₄ : (extractBlockPool bpL.mp stA₄.mem).nSide = bp₀.nSide - 1 :=
    (congrArg BlockPoolState.nSide hex₄_raw).trans (hn_cp.trans (congrArg (· - 1) hn₁))
  have hst_tot : (Memory.spec 0).clientState s₁ (bpPopBktPrepAndShrinkProg (bpL.toCtx, b)) =
      stA₄ := by
    unfold bpPopBktPrepAndShrinkProg; dsimp only [BlockPoolLayout.toCtx]
    rw [StateTransitionSpec.clientState_bind, hres₁, hstA₁,
      StateTransitionSpec.clientState_bind, hstA₂,
      StateTransitionSpec.clientState_bind, hstA₃, hstA₄]
  refine ⟨?_, by rw [hst_tot]; exact hfr₄, by rw [hst_tot, hex₄_raw]; exact hsi₄,
    by rw [hst_tot]; exact hns_s₄⟩
  unfold bpPopBktPrepAndShrinkProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpPrepPopMetaProg hm)) fun hc1 => ?_
  rw [hres₁]
  refine SlotCoupledStep.bind_prog (bpExecOptSwap_coupled hc1 hsw_lt) fun hc2 => ?_
  refine SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoPopBack hc2 hn_pos) fun hc3 => ?_
  exact SlotCoupledStep.of_confinedTo hc3 (confinedTo_bpCommitPopMetaProg hm)

/-- `bpPopBktBackRawProg` transitions `SlotStateCoupled` from `bp.nSide` to `bp.nSide - 1`. -/
theorem bpPopBktBackRaw_coupled {M : ℕ → Prop} {bpL : BlockPoolLayout} {b : ℕ}
    {s₁ s₂ : Memory.State}
    (hv : bpL.Valid bpL.mp.w s₁.frontier)
    (hm : BpMetaConf M bpL.mp.toCtx)
    (hbal : (extractBlockPool bpL.mp s₁.mem).Balanced)
    (hn_le : (extractBlockPool bpL.mp s₁.mem).nSide ≤ bpL.mp.nCap)
    (hb : b < bpL.mp.M) (hcnt : 0 < (extractBlockPool bpL.mp s₁.mem).bktCount b)
    (hc : SlotStateCoupled M bpL.io (extractBlockPool bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M bpL.io ((extractBlockPool bpL.mp s₁.mem).nSide - 1) s₁ s₂
      (bpPopBktBackRawProg (bpL.toCtx, b)) := by
  set bp₀ := extractBlockPool bpL.mp s₁.mem
  obtain ⟨hps_cs, hfr₄, hsi₄, hns₄⟩ :=
    bpPopBktPrepAndShrink_coupled hv hm hbal hn_le hb hcnt hc
  set sA₄ := (Memory.spec 0).clientState s₁ (bpPopBktPrepAndShrinkProg (bpL.toCtx, b))
  have hv₄ : bpL.Valid bpL.mp.w sA₄.frontier := by rw [hfr₄]; exact hv
  have hn₄_le : (extractBlockPool bpL.mp sA₄.mem).nSide ≤ bpL.mp.nCap := by
    rw [hns₄]; exact (Nat.sub_le _ 1).trans hn_le
  change SlotCoupledStep M bpL.io (bp₀.nSide - 1) s₁ s₂
    (do
      bpPopBktPrepAndShrinkProg (bpL.toCtx, b)
      bpRunBktTicks16Prog (bpL.toCtx, b)
      bpRunTopClean16Prog bpL.toCtx)
  refine SlotCoupledStep.bind_prog hps_cs fun hc4 => ?_
  have hb16_cs := bpRunBktTicks16_coupled hv₄ hm hsi₄ hb hn₄_le (hc4.cast_n hns₄.symm)
  obtain ⟨hfr₅_rel, hex₅, hsi₅, hn₅, _, _, _⟩ :=
    bpRunBktTicks16Prog_spec hv₄ hsi₄ hb hn₄_le (hc4.cast_n hns₄.symm).inv₁
  set sA₅ := (Memory.spec 0).clientState sA₄ (bpRunBktTicks16Prog (bpL.toCtx, b))
  have hfr₅ : sA₅.frontier = s₁.frontier := hfr₅_rel.trans hfr₄
  have hns₅ : (extractBlockPool bpL.mp sA₅.mem).nSide = bp₀.nSide - 1 :=
    (congrArg BlockPoolState.nSide hex₅).trans (hn₅.trans hns₄)
  rw [Nat.sub_self] at hsi₅
  refine SlotCoupledStep.bind_prog (hb16_cs.cast_n hns₄) fun hc5 => ?_
  have hv₅ : bpL.Valid bpL.mp.w sA₅.frontier := by rw [hfr₅]; exact hv
  have hsi₅' : (extractBlockPool bpL.mp sA₅.mem).StepInv b 0 := by rw [hex₅]; exact hsi₅
  have hn₅_le : (extractBlockPool bpL.mp sA₅.mem).nSide ≤ bpL.mp.nCap := by
    rw [hns₅]; exact (Nat.sub_le _ 1).trans hn_le
  exact (bpRunTopClean16_coupled (b₀ := b) hv₅ hm hsi₅' hn₅_le
    (hc5.cast_n hns₅.symm)).cast_n hns₅

private theorem clientState_fbOwnerOfProg (mp : BpMetaLayout) (p : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientState st (fbOwnerOfProg (mp.toCtx, p)) = st := by
  unfold fbOwnerOfProg fbOwnerOfProg.bpGetMKFromCtxProg fbOwnerOfProg.bpGetNcapFromCtxProg
  dsimp only [BpMetaLayout.toCtx]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg]
  split_ifs
  · exact clientState_bpReadSlabOwnerProg _ st
  · exact clientState_bpReadTailDirRawProg _ st
  · rfl
  · rfl

private theorem fbScanProg_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {bkt q_u : ℕ} {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    let n := (extractFallback mp s₁.mem).nSide
    SlotCoupledStep M io n s₁ s₂ (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u))) ∧
    (Memory.spec 0).clientState s₁ (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u))) = s₁ ∧
    (((Memory.spec 0).clientResult s₁ (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))).1 = 1 →
      ((Memory.spec 0).clientResult s₁ (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))).2.1 <
        n) := by
  dsimp only
  set n := (extractFallback mp s₁.mem).nSide
  have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) = n := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  have hown_st := clientState_fbOwnerOfProg mp
  have hloop := SlotCoupledStep.iterate_fuel
    (M := M) (io := io) (n := n) (body := fbScanStepProg)
    ((mp.toCtx, io.toCtx), (n, (bkt, q_u)))
    (fun _ acc st => st = s₁ ∧ (acc.1.2 = 1 → acc.2.1 < n))
    (fun _ ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩ st₁ st₂ ⟨hst_eq, hhit⟩ hc_st => by
      subst st₁
      unfold fbScanStepProg; dsimp only
      have hcs : SlotCoupledStep M io n s₁ st₂
          (if cur < n then do
            let b_cur ← fbOwnerOfProg (mp.toCtx, cur)
            let qv ← slotIoReadRawProg (io.toCtx, cur)
            if found = 0 ∧ b_cur = bkt ∧ qv.1 = q_u then pure ((cur + 1, 1), (cur, qv.2))
            else pure ((cur + 1, found), (hitP, hitVal))
          else do
            let _ ← bpReadScalarProg (mp.toCtx, 1)
            pure ((cur, found), (hitP, hitVal))) :=
        SlotCoupledStep.ite_prog
          (fun hlt => SlotCoupledStep.bind_prog
            (SlotCoupledStep.of_confinedTo hc_st (cf_fbOwnerOfProg hm)) fun hc_a =>
            SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoRead hc_a hlt) fun hc_b =>
            SlotCoupledStep.ite_prog
              (fun _ => SlotCoupledStep.pure_prog hc_b _)
              (fun _ => SlotCoupledStep.pure_prog hc_b _))
          (fun _ => SlotCoupledStep.bind_prog
            (SlotCoupledStep.of_confinedTo hc_st (confinedTo_bpReadScalarProg hm))
            fun hc_a => SlotCoupledStep.pure_prog hc_a _)
      refine ⟨hcs, ?_⟩
      by_cases hlt : cur < n
      · obtain ⟨_, hr_st⟩ := slotIoReadProg_spec hc_st.inv₁ hlt
        unfold slotIoReadProg at hr_st
        rw [ite_eq_left hlt, StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientState_bind, hown_st,
          StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind, hr_st]
        rcases (Memory.spec 0).clientResult s₁ (slotIoReadRawProg (io.toCtx, cur)) with ⟨q, v⟩
        dsimp only
        split_ifs
        · exact ⟨rfl, fun _ => hlt⟩
        · exact ⟨rfl, hhit⟩
      · rw [ite_eq_right hlt, StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
        exact ⟨rfl, hhit⟩)
    n ((0, 0), (0, 0)) s₁ s₂ ⟨rfl, fun h => absurd h (by decide)⟩ hc
  unfold fbScanProg fbScanLoopProg
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [BpMetaLayout.toCtx] at *
    refine SlotCoupledStep.bind_prog
      (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm)) fun hc1 => ?_
    rw [clientState_bpReadScalarProg] at hc1 ⊢
    rw [hns_res]
    refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc1 _)
    simp only [pure_bind]
    exact SlotCoupledStep.bind_prog hloop.1 fun hc2 => SlotCoupledStep.pure_prog hc2 _
  · dsimp only [BpMetaLayout.toCtx] at *
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, hns_res]
    split_ifs
    · simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
      exact hloop.2.1
    · rfl
  · conv_lhs => dsimp only [BpMetaLayout.toCtx]
    conv_rhs => dsimp only [BpMetaLayout.toCtx]
    dsimp only [BpMetaLayout.toCtx] at hns_res
    have hrd_st : (Memory.spec 0).clientState s₁ (bpReadScalarProg (mp.toCtx, 1)) = s₁ :=
      clientState_bpReadScalarProg _ s₁
    dsimp only [BpMetaLayout.toCtx] at hrd_st
    simp only [StateTransitionSpec.clientResult_bind, hrd_st, hns_res]
    by_cases hle : n ≤ mp.nCap
    · simp only [ite_eq_left hle, pure_bind, StateTransitionSpec.clientResult_bind]
      have hst_loop := hloop.2.1
      dsimp only [BpMetaLayout.toCtx] at hst_loop
      rw [hst_loop]
      exact hloop.2.2
    · simp only [ite_eq_right hle]; rintro ⟨⟩

private theorem fbSwapRange_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {n b₁ b₂ len : ℕ} {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx) (hb₁ : b₁ + len ≤ n) (hb₂ : b₂ + len ≤ n)
    (hc : SlotStateCoupled M io n s₁ s₂) :
    SlotCoupledStep M io n s₁ s₂ (fbSwapRangeProg (((mp.toCtx, io.toCtx), (b₁, b₂)), len)) := by
  have hloop := SlotCoupledStep.iterate_fuel
    (M := M) (io := io) (n := n) (body := fbSwapRangeStepProg)
    ((mp.toCtx, io.toCtx), (b₁, b₂))
    (fun k cur _ => cur + k ≤ len)
    (fun k cur st₁ st₂ hcur hc_st => by
      have hcur_lt : cur < len := by omega
      unfold fbSwapRangeStepProg; dsimp only [BpMetaLayout.toCtx] at *
      have hcs : SlotCoupledStep M io n st₁ st₂
          (do
            let _ ← bpReadScalarProg (mp.toCtx, 1)
            if cur < mp.nCap then
              if b₁ < mp.nCap - cur then
                if b₂ < mp.nCap - cur then do
                  let p₁ ← pure (b₁ + cur)
                  let p₂ ← pure (b₂ + cur)
                  slotIoSwapRawProg (io.toCtx, (p₁, p₂))
                  pure (cur + 1)
                else pure cur
              else pure cur
            else pure cur) :=
        SlotCoupledStep.bind_prog
          (SlotCoupledStep.of_confinedTo hc_st (confinedTo_bpReadScalarProg hm)) fun hc_a =>
          SlotCoupledStep.ite_prog (fun _ =>
            SlotCoupledStep.ite_prog (fun _ =>
              SlotCoupledStep.ite_prog (fun _ => by
                simp only [pure_bind]
                exact SlotCoupledStep.bind_prog
                  (SlotCoupledStep.slotIoSwap hc_a (by omega) (by omega))
                  fun hc_b => SlotCoupledStep.pure_prog hc_b _)
              (fun _ => SlotCoupledStep.pure_prog hc_a _))
            (fun _ => SlotCoupledStep.pure_prog hc_a _))
          (fun _ => SlotCoupledStep.pure_prog hc_a _)
      refine ⟨hcs, ?_⟩
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg]
      split_ifs
      · simp only [pure_bind, StateTransitionSpec.clientResult_bind, prog_clientResult_pure]
        omega
      all_goals (rw [prog_clientResult_pure]; omega))
    len 0 s₁ s₂ (Nat.zero_add len).le hc
  unfold fbSwapRangeProg fbSwapRangeLoopProg; simp only [pure_bind]
  exact SlotCoupledStep.bind_prog hloop.1 fun hc1 => SlotCoupledStep.pure_prog hc1 ()

private theorem fbSwapTailSlots_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {n fbBase t₁ t₂ : ℕ} {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx) (ht₁ : fbBase + t₁ < n) (ht₂ : fbBase + t₂ < n)
    (hc : SlotStateCoupled M io n s₁ s₂) :
    SlotCoupledStep M io n s₁ s₂
      (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂))) := by
  unfold fbSwapTailSlotsProg fbReadTailPairProg fbWriteTailPairProg
  dsimp only [BpMetaLayout.toCtx] at *
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc ())
  exact SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc
      (ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ =>
        ConfinedTo.bind_prog (confinedTo_bpReadTailDirRawProg hm) fun _ => ConfinedTo.pure_prog _))
    fun hc1 => SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoSwap hc1 ht₁ ht₂)
    fun hc2 => SlotCoupledStep.of_confinedTo hc2
      (ConfinedTo.bind_prog (confinedTo_bpWriteTailDirRawProg hm) fun _ =>
        confinedTo_bpWriteTailDirRawProg hm)

private theorem fbFindMatchLoop_src_lt {mp : BpMetaLayout} {tl bS : ℕ} :
    ∀ fuel t found src (st : Memory.State),
      src < tl →
      ((Memory.spec 0).clientState st
        (iterate fbFindMatchStepProg (mp.toCtx, (tl, bS)) fuel (t, (found, src))) = st) ∧
      (((Memory.spec 0).clientResult st
        (iterate fbFindMatchStepProg (mp.toCtx, (tl, bS)) fuel (t, (found, src)))).2.2 < tl) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ hsrc; exact ⟨rfl, hsrc⟩
  | succ f ih =>
    intro t found src st hsrc
    have hst1 : (Memory.spec 0).clientState st
        (fbFindMatchStepProg ((mp.toCtx, (tl, bS)), (t, (found, src)))) = st := by
      unfold fbFindMatchStepProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg]
        split_ifs <;> rfl
      · rfl
    have hsrc1 : ((Memory.spec 0).clientResult st
        (fbFindMatchStepProg ((mp.toCtx, (tl, bS)), (t, (found, src))))).2.2 < tl := by
      unfold fbFindMatchStepProg
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg]
      by_cases hlt : t < tl
      · rw [ite_eq_left hlt, StateTransitionSpec.clientResult_bind,
          clientState_bpReadTailDirRawProg]
        split_ifs <;> [exact hlt; exact hsrc]
      · rw [ite_eq_right hlt]; exact hsrc
    unfold iterate
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hst1]
    rcases hr : (Memory.spec 0).clientResult st
      (fbFindMatchStepProg ((mp.toCtx, (tl, bS)), (t, (found, src)))) with ⟨t1, ⟨f1, src1⟩⟩
    rw [hr] at hsrc1
    exact ih t1 f1 src1 st hsrc1

private theorem fbPromoteOneBlock_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M io (extractFallback mp s₁.mem).nSide s₁ s₂
      (fbPromoteOneBlockProg (mp.toCtx, io.toCtx)) := by
  set n := (extractFallback mp s₁.mem).nSide
  have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) = n := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  unfold fbPromoteOneBlockProg fbPromoteCheckProg fbPromoteInnerCheckProg fbPromoteBodyProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) hns_res fun hc1 => ?_
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc1 (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) fun hc2 => ?_
  set fb0 := (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 10))
  dsimp only [BpMetaLayout.toCtx]
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  simp only [pure_bind]
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  set tl := n - fb0 * mp.K
  change SlotCoupledStep M io n s₁ _
    (do
      let hb ← fbFindHeavyBktLoopProg (((mp.toCtx, tl), (0, 0)), mp.M)
      let _ ← fbPartHeavyLoopProg ((((mp.toCtx, io.toCtx), (fb0 * mp.K, (tl, hb.2))), 0), mp.K)
      fbPromoteFinishProg ((mp.toCtx, (fb0, tl)), hb.2))
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc2 (cf_fbFindHeavyBktLoopProg hm)) fun hc3 => ?_
  set bStar :=
    ((Memory.spec 0).clientResult s₁
      (fbFindHeavyBktLoopProg (((mp.toCtx, tl), (0, 0)), mp.M))).2
  have hph := SlotCoupledStep.iterate_fuel
    (M := M) (io := io) (n := n) (body := fbPartHeavyStepProg)
    ((mp.toCtx, io.toCtx), (fb0 * mp.K, (tl, bStar)))
    (fun _ _ _ => True)
    (fun _ dst st₁ st₂ _ hc_st => by
      unfold fbPartHeavyStepProg
      refine ⟨SlotCoupledStep.bind_readOnly
        (SlotCoupledStep.of_confinedTo hc_st (confinedTo_bpReadScalarProg hm))
        (clientState_bpReadScalarProg _ st₁) fun hc_a =>
        SlotCoupledStep.ite_prog (fun hdst => by
          simp only [pure_bind]
          have hfm := fbFindMatchLoop_src_lt (mp := mp) (tl := tl) (bS := bStar)
            (tl - dst) dst 0 dst st₁ hdst
          have hfm_st : (Memory.spec 0).clientState st₁
              (fbFindMatchLoopProg (((mp.toCtx, (tl, bStar)), (dst, (0, dst))), tl - dst)) = st₁ :=
            hfm.1
          refine SlotCoupledStep.bind_readOnly
            (SlotCoupledStep.of_confinedTo hc_a (cf_fbFindMatchLoopProg hm))
            hfm_st fun hc_b => ?_
          have hsrc' : ((Memory.spec 0).clientResult st₁
              (fbFindMatchLoopProg
                (((mp.toCtx, (tl, bStar)), (dst, (0, dst))), tl - dst))).2.2 < tl := hfm.2
          exact SlotCoupledStep.bind_prog
            (fbSwapTailSlots_coupled hm (by omega) (by omega) hc_b)
            fun hc_c => SlotCoupledStep.pure_prog hc_c _)
        (fun _ => SlotCoupledStep.pure_prog hc_a _), trivial⟩)
    mp.K 0 _ _ trivial hc3
  unfold fbPartHeavyLoopProg; dsimp only
  exact SlotCoupledStep.bind_prog hph.1 fun hc4 =>
    SlotCoupledStep.of_confinedTo hc4 (cf_fbPromoteFinishProg hm)

private theorem fbMaybePromote_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M io (extractFallback mp s₁.mem).nSide s₁ s₂
      (fbMaybePromoteProg (mp.toCtx, io.toCtx)) := by
  unfold fbMaybePromoteProg fbMaybePromoteCheckProg fbMaybePromoteInnerProg
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) fun hc1 => ?_
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc1 (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) fun hc2 => ?_
  dsimp only [BpMetaLayout.toCtx]
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  simp only [pure_bind]
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  exact SlotCoupledStep.ite_prog
    (fun _ => fbPromoteOneBlock_coupled hm hc2)
    (fun _ => SlotCoupledStep.pure_prog hc2 ())

private theorem fbDemoteBlk_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {blk : ℕ} {s₁ s₂ : Memory.State}
    (hm : BpMetaConf M mp.toCtx)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M io (extractFallback mp s₁.mem).nSide s₁ s₂
      (fbDemoteBlkProg ((mp.toCtx, io.toCtx), blk)) := by
  set n := (extractFallback mp s₁.mem).nSide
  have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) = n := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  unfold fbDemoteBlkProg fbDemoteCheckProg fbDemoteInnerProg fbDemoteSwapProg fbDemoteSwapBodyProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) hns_res fun hc1 => ?_
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc1 (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) fun hc2 => ?_
  set fb0 := (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 10))
  dsimp only [BpMetaLayout.toCtx]
  refine SlotCoupledStep.ite_prog (fun hblk_lt => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  simp only [pure_bind]
  refine SlotCoupledStep.ite_prog (fun hfb_le => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  refine SlotCoupledStep.ite_prog (fun _ => ?_) (fun _ => SlotCoupledStep.pure_prog hc2 ())
  have hb1 : blk * mp.K + mp.K ≤ n := by
    have : (blk + 1) * mp.K ≤ fb0 * mp.K := Nat.mul_le_mul_right _ hblk_lt
    rw [Nat.add_one_mul] at this; omega
  have hb2 : (fb0 - 1) * mp.K + mp.K ≤ n := by
    have : (fb0 - 1 + 1) * mp.K = fb0 * mp.K := by congr 1; omega
    rw [Nat.add_one_mul] at this; omega
  have hrp : ConfinedTo M (fbReadBlkPairProg (mp.toCtx, (blk, fb0 - 1))) := by
    unfold fbReadBlkPairProg
    exact ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ =>
      ConfinedTo.bind_prog (confinedTo_bpReadSlabOwnerProg hm) fun _ => ConfinedTo.pure_prog _
  have hwp : ∀ os, ConfinedTo M (fbWriteBlkPairProg ((mp.toCtx, (blk, fb0 - 1)), os)) := by
    rintro ⟨_, _⟩; unfold fbWriteBlkPairProg
    exact ConfinedTo.bind_prog (confinedTo_bpWriteSlabOwnerProg hm) fun _ =>
      confinedTo_bpWriteSlabOwnerProg hm
  refine SlotCoupledStep.bind_prog ?_ fun hc3 =>
    SlotCoupledStep.of_confinedTo hc3 (cf_fbDemoteTailProg hm)
  exact SlotCoupledStep.ite_prog (fun _ =>
    SlotCoupledStep.ite_prog (fun _ =>
      SlotCoupledStep.bind_prog (SlotCoupledStep.of_confinedTo hc2 hrp) fun hc3 =>
        SlotCoupledStep.bind_prog (fbSwapRange_coupled hm hb1 hb2 hc3) fun hc4 =>
        SlotCoupledStep.bind_prog (SlotCoupledStep.of_confinedTo hc4 (hwp _)) fun hc5 =>
        SlotCoupledStep.pure_prog hc5 _)
    (fun _ => SlotCoupledStep.pure_prog hc2 0))
    (fun _ => SlotCoupledStep.pure_prog hc2 0)

private theorem fbPopTailAt_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {p : ℕ} {s₁ s₂ : Memory.State}
    (hmv : mp.Valid mp.w s₁.frontier)
    (hm : BpMetaConf M mp.toCtx)
    (hfb : (extractFallback mp s₁.mem).Valid)
    (hns_le : (extractFallback mp s₁.mem).nSide ≤ mp.nCap)
    (hp_ge : (extractFallback mp s₁.mem).fullBlocks * mp.K ≤ p)
    (hp_lt : p < (extractFallback mp s₁.mem).nSide)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M io ((extractFallback mp s₁.mem).nSide - 1) s₁ s₂
      (fbPopTailAtProg ((mp.toCtx, io.toCtx), p)) := by
  set n := (extractFallback mp s₁.mem).nSide
  set fb0 := (extractFallback mp s₁.mem).fullBlocks
  have hK_pos : 0 < mp.K := by have := hmv.K_ge; omega
  have hfb_div : fb0 ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK_pos).mpr (hp_ge.trans (hp_lt.le.trans hns_le))
  have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) = n := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  have hfb_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 10)) = fb0 := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left (Or.inr ⟨by decide, by decide⟩)]; rfl
  unfold fbPopTailAtProg fbPopTailCheckProg fbPopTailInnerProg fbPopBackAndDecProg
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm)) fun hc1 => ?_
  rw [clientState_bpReadScalarProg] at hc1 ⊢
  rw [hns_res]
  refine SlotCoupledStep.bind_prog
    (SlotCoupledStep.of_confinedTo hc1 (confinedTo_bpReadScalarProg hm)) fun hc2 => ?_
  rw [clientState_bpReadScalarProg] at hc2 ⊢
  rw [hfb_res]
  dsimp only [BpMetaLayout.toCtx] at *
  rw [ite_eq_left hns_le, ite_eq_left hfb_div]; simp only [pure_bind]
  rw [ite_eq_left hp_ge, ite_eq_left hp_lt]
  have ht1 : fb0 * mp.K + (p - fb0 * mp.K) < n := by omega
  have ht2 : fb0 * mp.K + (n - 1 - fb0 * mp.K) < n := by
    have := hfb.blocks_le; change fb0 * mp.K ≤ n at this; omega
  exact SlotCoupledStep.bind_prog (fbSwapTailSlots_coupled hm ht1 ht2 hc2) fun hc3 =>
    SlotCoupledStep.bind_prog (SlotCoupledStep.slotIoPopBack hc3 (by omega)) fun hc4 =>
    SlotCoupledStep.of_confinedTo hc4 (confinedTo_bpWriteScalarProg hm)

private theorem fbDeleteSlot_coupled {M : ℕ → Prop} {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits hitP : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)}
    {s₁ s₂ : Memory.State}
    (hmv : mp.Valid mp.w s₁.frontier)
    (hm : BpMetaConf M mp.toCtx)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s₁.mem).Valid)
    (hns_le : (extractFallback mp s₁.mem).nSide ≤ mp.nCap)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s₁.mem).nSide
      (extractFallback mp s₁.mem).owner (slotIoPairAt io s₁.mem) s_abs)
    (hp_lt : hitP < (extractFallback mp s₁.mem).nSide)
    (hc : SlotStateCoupled M io (extractFallback mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M io ((extractFallback mp s₁.mem).nSide - 1) s₁ s₂
      (fbDeleteSlotProg ((mp.toCtx, io.toCtx), hitP)) := by
  set n := (extractFallback mp s₁.mem).nSide
  set fb0 := (extractFallback mp s₁.mem).fullBlocks
  have hK_pos : 0 < mp.K := by have := hmv.K_ge; omega
  have hoff_lt : hitP % mp.K < mp.K := Nat.mod_lt hitP hK_pos
  have hfb_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 10)) = fb0 := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left (Or.inr ⟨by decide, by decide⟩)]; rfl
  unfold fbDeleteSlotProg fbDemoteAndPopProg fbDemotePopRunProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) hfb_res fun hc1 => ?_
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_confinedTo hc1 (confinedTo_bpDivModKProg M _))
    (clientState_bpDivModKProg _ s₁) (by rw [clientResult_bpDivModK]) fun hc2 => ?_
  by_cases hlt_fb : hitP / mp.K < fb0
  · rw [ite_eq_left hlt_fb]
    dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left hoff_lt]
    change SlotCoupledStep M io (n - 1) s₁ _
      (do
        fbMaybePromoteProg (mp.toCtx, io.toCtx)
        let fb1 ← bpReadScalarProg (mp.toCtx, 10)
        if hitP / mp.K < fb1 then
          if fb1 ≤ mp.nCap / mp.K then do
            let lastSlot ← pure ((fb1 - 1) * mp.K + hitP % mp.K)
            fbDemoteBlkProg ((mp.toCtx, io.toCtx), hitP / mp.K)
            fbPopTailAtProg ((mp.toCtx, io.toCtx), lastSlot)
          else pure ()
        else pure ())
    obtain ⟨hfr_mp, hns_mp, hfb_le1, htl_plus1, hval1, hio1, href1, _, _⟩ :=
      fbMaybePromoteProg_spec hmv hc2.valid₁ hdisj hfb hns_le hc2.inv₁ href
    set stA₁ := (Memory.spec 0).clientState s₁ (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    set fb1 := (extractFallback mp stA₁.mem).fullBlocks
    have hblk_fb1 : hitP / mp.K < fb1 := lt_of_lt_of_le hlt_fb hfb_le1
    have hfb1_div : fb1 ≤ mp.nCap / mp.K := by
      have hb1 := hval1.blocks_le
      change fb1 * mp.K ≤ (extractFallback mp stA₁.mem).nSide at hb1
      exact (Nat.le_div_iff_mul_le hK_pos).mpr (hb1.trans (hns_mp ▸ hns_le))
    have hfb1_res : (Memory.spec 0).clientResult stA₁ (bpReadScalarProg (mp.toCtx, 10)) = fb1 := by
      unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
      rw [ite_eq_left (Or.inr ⟨by decide, by decide⟩)]; rfl
    refine SlotCoupledStep.bind_prog (fbMaybePromote_coupled hm hc2) fun hc3 => ?_
    change SlotStateCoupled M io n stA₁ _ at hc3
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc3 (confinedTo_bpReadScalarProg hm))
      (clientState_bpReadScalarProg _ stA₁) hfb1_res fun hc4 => ?_
    rw [ite_eq_left hblk_fb1, ite_eq_left hfb1_div]; simp only [pure_bind]
    have hmv₁ : mp.Valid mp.w stA₁.frontier := by rw [hfr_mp]; exact hmv
    have hvio₁ : io.Valid io.pgL.w stA₁.frontier := by rw [hfr_mp]; exact hc2.valid₁
    have hns₁_le : (extractFallback mp stA₁.mem).nSide ≤ mp.nCap := by rw [hns_mp]; exact hns_le
    have hio₁' : io.StateInv (extractFallback mp stA₁.mem).nSide 0 stA₁.mem := by
      rw [hns_mp]; exact hio1
    have href₁' : PoolItemsRefines U V bBits hBkt (extractFallback mp stA₁.mem).nSide
        (extractFallback mp stA₁.mem).owner (slotIoPairAt io stA₁.mem) s_abs := by
      rw [hns_mp]; exact href1
    obtain ⟨hfr_dm, hns_dm, hfb_dm, hval_dm, _, _, _, _, _⟩ :=
      fbDemoteBlkProg_spec hmv₁ hvio₁ hdisj hval1 hns₁_le htl_plus1 hblk_fb1 hio₁' href₁'
    set stA₂ := (Memory.spec 0).clientState stA₁
      (fbDemoteBlkProg ((mp.toCtx, io.toCtx), hitP / mp.K))
    have hns_stA₂ : (extractFallback mp stA₂.mem).nSide = n := hns_dm.trans hns_mp
    refine SlotCoupledStep.bind_prog
      ((fbDemoteBlk_coupled hm (hc4.cast_n hns_mp.symm)).cast_n hns_mp) fun hc5 => ?_
    change SlotStateCoupled M io n stA₂ _ at hc5
    have hp_ge2 : (extractFallback mp stA₂.mem).fullBlocks * mp.K ≤
        (fb1 - 1) * mp.K + hitP % mp.K := by
      rw [hfb_dm]; exact Nat.le_add_right _ _
    have hp_lt2 : (fb1 - 1) * mp.K + hitP % mp.K < (extractFallback mp stA₂.mem).nSide := by
      have hfb1_pos : 0 < fb1 := lt_of_le_of_lt (Nat.zero_le _) hblk_fb1
      have hb1 : fb1 * mp.K ≤ n := by
        have h := hval1.blocks_le
        change fb1 * mp.K ≤ (extractFallback mp stA₁.mem).nSide at h
        rwa [hns_mp] at h
      have hsplit : (fb1 - 1) * mp.K + mp.K = fb1 * mp.K := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hfb1_pos]
      rw [hns_stA₂]; omega
    have hmv₂ : mp.Valid mp.w stA₂.frontier := by rw [hfr_dm, hfr_mp]; exact hmv
    have hns₂_le : (extractFallback mp stA₂.mem).nSide ≤ mp.nCap := by
      rw [hns_stA₂]; exact hns_le
    exact (fbPopTailAt_coupled hmv₂ hm hval_dm hns₂_le hp_ge2 hp_lt2
      (hc5.cast_n hns_stA₂.symm)).cast_n (congrArg (· - 1) hns_stA₂)
  · rw [ite_eq_right hlt_fb]
    have hp_ge : fb0 * mp.K ≤ hitP := by
      have hge : fb0 ≤ hitP / mp.K := Nat.le_of_not_lt hlt_fb
      have hdm := Nat.div_add_mod hitP mp.K
      have := Nat.mul_le_mul_right mp.K hge
      rw [Nat.mul_comm] at hdm; omega
    exact fbPopTailAt_coupled hmv hm hfb hns_le hp_ge hp_lt hc2

/-- `fallbackDeleteProg` preserves `SlotStateCoupled`
(`n' = (extractFallback mp s₁'.mem).nSide`). -/
theorem fallbackDelete_coupled {M : ℕ → Prop} {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {u_val : ℕ} {s₁ s₂ : Memory.State}
    (hv : fl.Valid w s₁.frontier)
    (hf : FeistelConf M fl.feistelCtx)
    (hm : BpMetaConf M fl.bpL.mp.toCtx)
    (hinv : fl.StateInv 0 θ_bkt s₁.mem s_abs)
    (hc : SlotStateCoupled M fl.bpL.io (extractFallback fl.bpL.mp s₁.mem).nSide s₁ s₂) :
    let s₁' := (Memory.spec 0).clientState s₁
      (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val))
    SlotCoupledStep M fl.bpL.io (extractFallback fl.bpL.mp s₁'.mem).nSide s₁ s₂
      (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val)) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  have hmv : mp.Valid mp.w s₁.frontier := by
    have := hv.bp_valid.mp_valid
    rwa [← this.w_eq]
  have hfs_st : (Memory.spec 0).clientState s₁ (feistelSplitBoundedProg (fl.feistelCtx, u_val)) =
      s₁ := by
    unfold feistelSplitBoundedProg; dsimp only [FallbackLayout.feistelCtx]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]
    rfl
  rcases hbq : (Memory.spec 0).clientResult s₁ (feistelSplitBoundedProg (fl.feistelCtx, u_val)) with
    ⟨bkt, q_u⟩
  obtain ⟨_, hscan_st, hscan_lt⟩ := fbScanProg_coupled (bkt := bkt) (q_u := q_u) hm hc
  rcases hr : (Memory.spec 0).clientResult s₁ (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u))) with
    ⟨f, ⟨hitP, hitVal⟩⟩
  rw [hr] at hscan_lt
  by_cases hf1 : f = 1
  · have hp_lt : hitP < (extractFallback mp s₁.mem).nSide := hscan_lt hf1
    obtain ⟨hu_lt, _, hb_hit, hq_hit, _⟩ := hinv.refines.slot_key_val hp_lt
    let uHit : Fin fl.U := ⟨_, hu_lt⟩
    obtain ⟨_, hns_del, _, _, _, _, _⟩ :=
      fbDeleteSlotProg_spec hmv hc.valid₁ hv.bp_valid.disjoint hinv.fb_valid hinv.nSide_le hc.inv₁
        hinv.refines hp_lt uHit hb_hit.symm hq_hit.symm
    have hs1'_ns : (extractFallback mp
        ((Memory.spec 0).clientState s₁
          (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val))).mem).nSide =
        (extractFallback mp s₁.mem).nSide - 1 := by
      unfold fallbackDeleteProg; dsimp only [BlockPoolLayout.toCtx]
      rw [StateTransitionSpec.clientState_bind, hfs_st, hbq,
        StateTransitionSpec.clientState_bind, hscan_st, hr]; dsimp only
      rw [ite_eq_left hf1]; exact hns_del
    refine (?_ : SlotCoupledStep M fl.bpL.io ((extractFallback mp s₁.mem).nSide - 1) s₁ s₂
      (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val))).cast_n hs1'_ns.symm
    unfold fallbackDeleteProg; dsimp only [BlockPoolLayout.toCtx]
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (confinedTo_feistelSplitBoundedProg hf))
      hfs_st hbq fun hc1 => ?_
    refine SlotCoupledStep.bind_readOnly_eq
      (fbScanProg_coupled (bkt := bkt) (q_u := q_u) hm hc1).1 hscan_st hr fun hc2 => ?_
    dsimp only; rw [ite_eq_left hf1]
    exact fbDeleteSlot_coupled hmv hm hv.bp_valid.disjoint hinv.fb_valid hinv.nSide_le hinv.refines
      hp_lt hc2
  · have hs1'_ns : (extractFallback mp
        ((Memory.spec 0).clientState s₁
          (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val))).mem).nSide =
        (extractFallback mp s₁.mem).nSide := by
      unfold fallbackDeleteProg; dsimp only [BlockPoolLayout.toCtx]
      rw [StateTransitionSpec.clientState_bind, hfs_st, hbq,
        StateTransitionSpec.clientState_bind, hscan_st, hr]; dsimp only
      rw [ite_eq_right hf1]; rfl
    refine (?_ : SlotCoupledStep M fl.bpL.io (extractFallback mp s₁.mem).nSide s₁ s₂
      (fallbackDeleteProg ((fl.feistelCtx, fl.bpL.toCtx), u_val))).cast_n hs1'_ns.symm
    unfold fallbackDeleteProg; dsimp only [BlockPoolLayout.toCtx]
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (confinedTo_feistelSplitBoundedProg hf))
      hfs_st hbq fun hc1 => ?_
    refine SlotCoupledStep.bind_readOnly_eq
      (fbScanProg_coupled (bkt := bkt) (q_u := q_u) hm hc1).1 hscan_st hr fun hc2 => ?_
    dsimp only; rw [ite_eq_right hf1]
    exact SlotCoupledStep.pure_prog hc2 ()

/-- `fallbackPopAnyProg` (`0 < nSide`) pops the identical `(u, v)` pair and transitions
`SlotStateCoupled` from `nSide` to `nSide - 1`. -/
theorem fallbackPopAny_coupled {M : ℕ → Prop} {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s₁ s₂ : Memory.State}
    (hv : fl.Valid w s₁.frontier)
    (hf : FeistelConf M fl.feistelCtx)
    (hm : BpMetaConf M fl.bpL.mp.toCtx)
    (hinv : fl.StateInv 0 θ_bkt s₁.mem s_abs)
    (hpos : 0 < (extractFallback fl.bpL.mp s₁.mem).nSide)
    (hc : SlotStateCoupled M fl.bpL.io (extractFallback fl.bpL.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M fl.bpL.io ((extractFallback fl.bpL.mp s₁.mem).nSide - 1) s₁ s₂
      (fallbackPopAnyProg (fl.feistelCtx, fl.bpL.toCtx)) := by
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set n := (extractFallback mp s₁.mem).nSide
  have hmv : mp.Valid mp.w s₁.frontier := by
    have := hv.bp_valid.mp_valid
    rwa [← this.w_eq]
  have hns_res : (Memory.spec 0).clientResult s₁ (bpReadScalarProg (mp.toCtx, 1)) = n := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  have hown_st := clientState_fbOwnerOfProg mp (n - 1) s₁
  obtain ⟨hr_qv, hs_qv⟩ := slotIoReadProg_spec hc.inv₁ (show n - 1 < n by omega)
  unfold slotIoReadProg at hr_qv hs_qv
  obtain ⟨hu_lt, _, hb_last, hq_last, _⟩ := hinv.refines.slot_key_val (show n - 1 < n by omega)
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM_ge : 2 ≤ 2 ^ bWhp fl.N := by
      have h1 := hv.bp_valid.mp_valid.M_ge
      rw [hv.mp_eq] at h1; exact h1
    by_contra hz
    have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM_ge; omega
  have hle_kb : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hqLim_eq : redWidthWhp fl.U - bWhp fl.N = quotBitsWhp fl.U fl.N := by rw [hrw_eq]; rfl
  have hb_w0 : bWhp fl.N ≤ redWidthWhp fl.U := hrw_eq ▸ hle_kb
  have hqlim_w : redWidthWhp fl.U - bWhp fl.N < mp.w := by
    have hsum : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
      unfold quotBitsWhp; rw [Nat.sub_add_cancel hle_kb]
      exact Nat.clog_le_of_le_pow hv.fits_U.le
    rw [hqLim_eq, hv.bp_valid.mp_valid.w_eq.symm]; omega
  have hq_lim : (slotIoPairAt io s₁.mem (n - 1)).1 < 1 <<< (redWidthWhp fl.U - bWhp fl.N) := by
    rw [hqLim_eq, Nat.shiftLeft_eq, one_mul, ← hq_last]
    exact keyQuotient_bWhp_lt hv.N_le_U ⟨_, hu_lt⟩
  have hrec_st : ∀ b_l q_l,
      (Memory.spec 0).clientState s₁
        (feistelReconBoundedProg (fl.feistelCtx, (b_l, q_l))) = s₁ := by
    intro b_l q_l
    unfold feistelReconBoundedProg; dsimp only [FallbackLayout.feistelCtx]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]
    rfl
  unfold fallbackPopAnyProg; dsimp only [BlockPoolLayout.toCtx]
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_confinedTo hc (confinedTo_bpReadScalarProg hm))
    (clientState_bpReadScalarProg _ s₁) hns_res fun hc1 => ?_
  rw [ite_eq_left hpos]; simp only [pure_bind]
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc1 (cf_fbOwnerOfProg hm))
    hown_st fun hc2 => ?_
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.slotIoRead hc2 (by omega))
    hs_qv hr_qv fun hc3 => ?_
  change SlotCoupledStep M fl.bpL.io (n - 1) s₁ _
    (if bWhp fl.N ≤ redWidthWhp fl.U then do
      let qLim ← pure (redWidthWhp fl.U - bWhp fl.N)
      if qLim < mp.w then
        if (slotIoPairAt io s₁.mem (n - 1)).1 < 1 <<< qLim then do
          let u_val ← feistelReconBoundedProg
            (fl.feistelCtx,
              ((Memory.spec 0).clientResult s₁ (fbOwnerOfProg (mp.toCtx, n - 1)),
               (slotIoPairAt io s₁.mem (n - 1)).1))
          fbDeleteSlotProg ((mp.toCtx, io.toCtx), n - 1)
          pure (u_val, (slotIoPairAt io s₁.mem (n - 1)).2)
        else pure (0, 0)
      else pure (0, 0)
    else pure (0, 0))
  rw [ite_eq_left hb_w0]; simp only [pure_bind]
  rw [ite_eq_left hqlim_w, ite_eq_left hq_lim]
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_confinedTo hc3 (confinedTo_feistelReconBoundedProg hf))
    (hrec_st _ _) fun hc4 => ?_
  exact SlotCoupledStep.bind_prog
    (fbDeleteSlot_coupled hmv hm hv.bp_valid.disjoint hinv.fb_valid hinv.nSide_le hinv.refines
      (by omega) hc4)
    fun hc5 => SlotCoupledStep.pure_prog hc5 _

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
