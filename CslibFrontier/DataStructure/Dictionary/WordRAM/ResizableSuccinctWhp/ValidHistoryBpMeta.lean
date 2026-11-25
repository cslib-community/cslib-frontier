/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolStepProg
import Mathlib.Tactic.Ring

/-!
# Memory History Admissibility (`ValidHistory`) for Hash and Block-Pool Metadata Programs

This module proves `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` for every
public `Memory.Prog` operation exported by `LargeMetaProg`, `LargeBlockPoolMetaProg`, and
`LargeBlockPoolStepProg`, discharging the memory history admissibility obligations needed by
`Realizes.code_spec` without modifying any upstream module. The proofs unfold the unexposed
program bodies via private `import all` and reduce every memory access to raw bounded
`Memory.read`/`Memory.write` checks, `validHistory_readPackedCompGen`, and
`validHistory_writePackedCompGen`.

## Main results

* `validHistory_subClampProg`, `validHistory_oddMulReducedProg`,
  `validHistory_evalSaltedBoundedProg`, `validHistory_feistelSplitBoundedProg`,
  `validHistory_feistelReconBoundedProg`: hash and modular arithmetic gadgets (`LargeMetaProg`).
* `validHistory_bpInitZeroedProg`, `validHistory_bpReadBktCountProg`,
  `validHistory_bpActCurProg`, `validHistory_bpEffBlkProg`, `validHistory_bpPhysOfTailProg`,
  `validHistory_bpToPhysRemProg`, `validHistory_bpToPhysProg`, `validHistory_bpOwnerOfTailProg`,
  `validHistory_bpOwnerOfNonSlabProg`, `validHistory_bpOwnerOfProg`: block-pool metadata accessors,
  arithmetic helpers, and lookup programs (`LargeBlockPoolMetaProg`).
* `validHistory_bpBktTickMetaProg`, `validHistory_bpTopCleanMetaProg`,
  `validHistory_bpRawPostAppendMetaProg`, `validHistory_bpPrepPopMetaProg`,
  `validHistory_bpCommitPopMetaProg`: block-pool rebalance and update metadata steps
  (`LargeBlockPoolStepProg`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: `ValidHistory` Combinators -/

private theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run hp

private theorem frontier_le_clientState {α : Type} (w : ℕ) (s : Memory.State)
    (p : Memory.Prog α) :
    s.frontier ≤ ((Memory.spec 0).clientState s p).frontier := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact Memory.frontier_le_run s _

private theorem validHistory_bind_of_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq⟩

private theorem validHistory_bind_ro {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq _ _ (frontier_le_clientState w s p)⟩

private theorem validHistory_bind_wf {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq _ _ (wellFormed_clientState hwf hp) (frontier_le_clientState w s p)⟩

private theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (if c then p₁ else p₂)) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

private theorem bpMetaLayout_valid_mono {mp : BpMetaLayout} {w fr₁ fr₂ : ℕ}
    (h : mp.Valid w fr₁) (hle : fr₁ ≤ fr₂) : mp.Valid w fr₂ :=
  { h with frontier_ge := h.frontier_ge.trans hle }

private theorem validHistory_bp_ro {α β : Type} {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', (BpMetaLayout.ofCtx ctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_ro hp fun a s' hfr' => hq a s' (bpMetaLayout_valid_mono hv hfr')

private theorem validHistory_bp_wf {α β : Type} {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → (BpMetaLayout.ofCtx ctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_wf hwf hp fun a s' hwf' hfr' =>
    hq a s' hwf' (bpMetaLayout_valid_mono hv hfr')

/-! ## Section 2: `LargeMetaProg` `ValidHistory` Proofs -/

/-- Unconditional memory history admissibility for `subClampProg` (pure arithmetic). -/
theorem validHistory_subClampProg (w : ℕ) (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subClampProg p)) := by
  unfold subClampProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `oddMulReducedProg` (pure arithmetic). -/
theorem validHistory_oddMulReducedProg (w : ℕ) (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (oddMulReducedProg x)) := by
  rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold oddMulReducedProg limbMasksProg halfMulModBoundedProg
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_subClampProg w _ _) fun _ _ _ => trivial

private theorem dtInnerLoop_valid {w hashBase c_tab d_tab b_char j : ℕ} {s : Memory.State}
    (hw : 0 < w) (hbc : b_char < w) (hj : j < d_tab)
    (hfr : hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤ s.frontier) :
    ∀ m i y r, i + m ≤ c_tab → y < 2 ^ b_char →
      let ctx : DtInnerCtx := (((hashBase, w), (c_tab, b_char)), j)
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate dtInnerStepProg ctx m ((i, y), r))) ∧
      (Memory.spec 0).clientState s (iterate dtInnerStepProg ctx m ((i, y), r)) = s ∧
      (Prod.snd (Prod.fst
        ((Memory.spec 0).clientResult s (iterate dtInnerStepProg ctx m ((i, y), r))))) <
        2 ^ b_char := by
  intro m
  induction m with
  | zero =>
    intro i y r _ hy
    exact ⟨trivial, rfl, hy⟩
  | succ m ih =>
    intro i y r him hy
    set ctx : DtInnerCtx := (((hashBase, w), (c_tab, b_char)), j)
    have hch_lt : r &&& ((1 <<< b_char) - 1) < 2 ^ b_char := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hrow_lt : j * (c_tab + 1) + i < d_tab * (c_tab + 1) := by
      calc j * (c_tab + 1) + i
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
    have hidx_lt : (j * (c_tab + 1) + i) * (1 <<< b_char) +
        (r &&& ((1 <<< b_char) - 1)) <
        BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
      have hsh : 1 <<< b_char = 2 ^ b_char := by rw [Nat.shiftLeft_eq, one_mul]
      calc (j * (c_tab + 1) + i) * (1 <<< b_char) + (r &&& ((1 <<< b_char) - 1))
          < (j * (c_tab + 1) + i) * (1 <<< b_char) + 2 ^ b_char := Nat.add_lt_add_left hch_lt _
        _ = (j * (c_tab + 1) + i + 1) * 2 ^ b_char := by rw [hsh]; ring
        _ ≤ d_tab * (c_tab + 1) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow_lt
        _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
            unfold BitPackedDoubleTabulation.topEntries; ring
    have hstep_vh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (dtInnerStepProg (ctx, ((i, y), r)))) := by
      unfold dtInnerStepProg
      simp only [pure_bind]
      refine validHistory_bind_ro
        (validHistory_readPackedCompGen
          ⟨BitPackedDoubleTabulation.topEntries c_tab d_tab b_char,
            hw, rfl, hbc.le, hidx_lt, hfr⟩)
        fun _ _ _ => trivial
    have hstep_st : (Memory.spec 0).clientState s (dtInnerStepProg (ctx, ((i, y), r))) = s := by
      unfold dtInnerStepProg
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
      rfl
    set y_next := y ^^^ readPacked (hashBase + 1) b_char w s.mem
      ((j * (c_tab + 1) + i) * (1 <<< b_char) + (r &&& ((1 <<< b_char) - 1)))
    have hstep_res : (Memory.spec 0).clientResult s (dtInnerStepProg (ctx, ((i, y), r))) =
        ((i + 1, y_next), r >>> b_char) := by
      unfold dtInnerStepProg
      dsimp only [ctx]
      simp only [pure_bind, prog_clientResult_bind, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, prog_clientResult_pure, y_next]
    have hy_next : y_next < 2 ^ b_char := Nat.xor_lt_two_pow hy (readPacked_lt ..)
    obtain ⟨hvh_m, hst_m, hy_m⟩ := ih (i + 1) y_next (r >>> b_char) (by omega) hy_next
    refine ⟨?_, ?_, ?_⟩
    · unfold iterate
      refine validHistory_bind_of_eq hstep_vh ?_
      rw [hstep_st, hstep_res]
      exact hvh_m
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res, hst_m]
    · unfold iterate
      rw [StateTransitionSpec.clientResult_bind, hstep_st, hstep_res]
      exact hy_m

private theorem dtOuterLoop_valid {w hashBase c_tab d_tab b_char M_out s_val rKey : ℕ}
    {s : Memory.State} (hw : 0 < w) (hbc : b_char < w) (hM : M_out ≤ w)
    (hs_lt : s_val < 2 ^ b_char)
    (hfr : hashBase + BitPackedDoubleTabulation.space w c_tab d_tab b_char M_out ≤ s.frontier) :
    let offBot_v := BitPackedDoubleTabulation.offBot w c_tab d_tab b_char
    let ctx : DtOuterCtx := (((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (s_val, rKey)))
    ∀ m j out, j + m ≤ d_tab →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate dtOuterStepProg ctx m (j, out))) := by
  intro offBot_v ctx m
  induction m with
  | zero =>
    intro j out _
    trivial
  | succ m ih =>
    intro j out hjm
    have hj : j < d_tab := by omega
    have hfr_top : hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤
        s.frontier := by
      unfold BitPackedDoubleTabulation.space at hfr; omega
    have hfr_bot : hashBase + offBot_v + BitPackedDoubleTabulation.botWords w d_tab b_char M_out ≤
        s.frontier := by
      dsimp only [offBot_v]
      unfold BitPackedDoubleTabulation.space at hfr
      unfold BitPackedDoubleTabulation.offBot
      omega
    obtain ⟨hin_vh, hin_st, hin_y⟩ :=
      dtInnerLoop_valid hw hbc hj hfr_top c_tab 0 0 rKey (by omega) (Nat.two_pow_pos b_char)
    have hrow_s : j * (c_tab + 1) + c_tab < d_tab * (c_tab + 1) := by
      calc j * (c_tab + 1) + c_tab
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
    have hidx_s : (j * (c_tab + 1) + c_tab) * (1 <<< b_char) + s_val <
        BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
      have hsh : 1 <<< b_char = 2 ^ b_char := by rw [Nat.shiftLeft_eq, one_mul]
      calc (j * (c_tab + 1) + c_tab) * (1 <<< b_char) + s_val
          < (j * (c_tab + 1) + c_tab) * 2 ^ b_char + 2 ^ b_char := by
            rw [hsh]; exact Nat.add_lt_add_left hs_lt _
        _ = (j * (c_tab + 1) + c_tab + 1) * 2 ^ b_char := by ring
        _ ≤ d_tab * (c_tab + 1) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow_s
        _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
            unfold BitPackedDoubleTabulation.topEntries; ring
    have hst_read : ∀ d', (Memory.spec 0).clientState s (readPackedCompGenProg d') = s := fun d' =>
      clientState_readPackedCompGenProg d' s
    set innerRes := (Memory.spec 0).clientResult s
      (iterate dtInnerStepProg (((hashBase, w), (c_tab, b_char)), j) c_tab ((0, 0), rKey))
    set y_acc := Prod.snd (Prod.fst innerRes)
    set t_salt := readPacked (hashBase + 1) b_char w s.mem
      ((j * (c_tab + 1) + c_tab) * (1 <<< b_char) + s_val)
    have hyj_lt : y_acc ^^^ t_salt < 2 ^ b_char := Nat.xor_lt_two_pow hin_y (readPacked_lt ..)
    have hidx2_lt : j * (1 <<< b_char) + (y_acc ^^^ t_salt) <
        BitPackedDoubleTabulation.botEntries d_tab b_char := by
      have hsh : 1 <<< b_char = 2 ^ b_char := by rw [Nat.shiftLeft_eq, one_mul]
      calc j * (1 <<< b_char) + (y_acc ^^^ t_salt)
          < j * 2 ^ b_char + 2 ^ b_char := by
            rw [hsh]; exact Nat.add_lt_add_left hyj_lt _
        _ = (j + 1) * 2 ^ b_char := by ring
        _ ≤ d_tab * 2 ^ b_char := Nat.mul_le_mul_right _ hj
    have hstep_vh : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (dtOuterStepProg (ctx, (j, out)))) := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      refine validHistory_bind_of_eq hin_vh ?_
      rw [hin_st]
      refine validHistory_bind_of_eq
        (validHistory_readPackedCompGen
          ⟨BitPackedDoubleTabulation.topEntries c_tab d_tab b_char,
            hw, rfl, hbc.le, hidx_s, hfr_top⟩) ?_
      rw [hst_read, clientResult_readPackedCompGenProg]
      exact validHistory_bind_ro
        (validHistory_readPackedCompGen
          ⟨BitPackedDoubleTabulation.botEntries d_tab b_char, hw, rfl, hM, hidx2_lt, hfr_bot⟩)
        fun _ _ _ => trivial
    have hstep_st : (Memory.spec 0).clientState s (dtOuterStepProg (ctx, (j, out))) = s := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hin_st,
        StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg,
        StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
      rfl
    have hfst : Prod.fst ((Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out)))) =
        j + 1 := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [prog_clientResult_bind, hin_st]
      simp only [prog_clientResult_bind, runClient_state_readPackedCompGenProg,
        prog_clientResult_pure]
    unfold iterate
    refine validHistory_bind_of_eq hstep_vh ?_
    rw [hstep_st]
    rcases hres : (Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out))) with ⟨j', out'⟩
    have hj'_eq : j' = j + 1 := by rw [← hfst, hres]
    subst hj'_eq
    exact ih (j + 1) out' (by omega)

/-- Memory history admissibility for `evalSaltedBoundedProg` under `EvalSaltedBoundedPre`
(read-only, so `Memory.WellFormed` is not required). -/
theorem validHistory_evalSaltedBoundedProg {w : ℕ} {inp : SaltedHashInput} {s : Memory.State}
    (hpre : EvalSaltedBoundedPre w inp s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (evalSaltedBoundedProg inp)) := by
  rcases inp with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
    ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, M_out⟩⟩⟩⟩, ⟨s_val, u_val⟩⟩
  obtain ⟨hw, hwVal, _hw₀, _hw₀_le, hbc, hM, hoff, _hα, hs_lt, _hu, _hd, _hc1, _htop, _hbot,
    hfr⟩ := hpre
  subst hwVal; subst hoff
  have hsp_pos := BitPackedDoubleTabulation.space_pos w c_tab d_tab b_char M_out
  have hbase_lt : hashBase < s.frontier := by omega
  have hread_vh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.read hashBase)) :=
    ⟨hbase_lt, trivial⟩
  have hread_st : (Memory.spec 0).clientState s (Memory.read hashBase) = s := rfl
  unfold evalSaltedBoundedProg dtOuterLoopProg
  refine validHistory_bind_of_eq hread_vh ?_
  rw [hread_st]
  refine validHistory_bind_of_eq (validHistory_oddMulReducedProg w _ s) ?_
  rw [clientState_oddMulReducedProg]
  simp only [pure_bind]
  exact validHistory_bind_ro
    (dtOuterLoop_valid hw hbc hM hs_lt hfr d_tab 0 0 (by omega))
    fun _ _ _ => trivial

/-- Memory history admissibility for `feistelSplitBoundedProg` under `FeistelSplitPre`
(read-only, so `Memory.WellFormed` is not required). -/
theorem validHistory_feistelSplitBoundedProg {w : ℕ} {x : FeistelHashCtx × ℕ} {s : Memory.State}
    (hpre : FeistelSplitPre w x s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (feistelSplitBoundedProg x)) := by
  rcases x with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
    ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, b_bits⟩⟩⟩⟩, u_val⟩
  obtain ⟨_hbb, _hu, heval⟩ := hpre
  unfold feistelSplitBoundedProg
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_evalSaltedBoundedProg heval) fun _ _ _ => trivial

/-- Memory history admissibility for `feistelReconBoundedProg` under `FeistelReconPre`
(read-only, so `Memory.WellFormed` is not required). -/
theorem validHistory_feistelReconBoundedProg {w : ℕ} {x : FeistelHashCtx × (ℕ × ℕ)}
    {s : Memory.State} (hpre : FeistelReconPre w x s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (feistelReconBoundedProg x)) := by
  rcases x with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
    ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, b_bits⟩⟩⟩⟩, ⟨bkt, q_val⟩⟩
  obtain ⟨_qb, _hbb, _hqbw, _hqlt, heval⟩ := hpre
  unfold feistelReconBoundedProg
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_evalSaltedBoundedProg heval) fun _ _ _ => trivial

/-! ## Section 3: `LargeBlockPoolMetaProg` `ValidHistory` Proofs -/

/-- Memory history admissibility for `bpInitZeroedProg` under `BpMetaLayout.Valid`. -/
theorem validHistory_bpInitZeroedProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpInitZeroedProg ctx)) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at ho32 hd1 hd2 hd3 hd4 hfr
  unfold bpInitZeroedProg
  simp only [pure_bind]
  exact ⟨⟨by omega, Nat.one_lt_two_pow hw.ne'⟩, trivial⟩

/-- Memory history admissibility for `bpReadScalarProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpReadScalarProg {w : ℕ} {ctx : BpMetaCtx} {idx : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadScalarProg (ctx, idx))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at ho32 hd1 hd2 hd3 hd4 hfr
  unfold bpReadScalarProg
  refine validHistory_ite (fun hk => ?_) (fun _ => trivial)
  have hlt : mb + idx < s.frontier := by omega
  exact ⟨hlt, trivial⟩

/-- Memory history admissibility for `bpWriteScalarProg` under `BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteScalarProg {w : ℕ} {ctx : BpMetaCtx} {idx val : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteScalarProg ((ctx, idx), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hnc_w := hv.nCap_lt_two_pow_w
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hnc_w ho32 hd1 hd2 hd3 hd4 hfr
  unfold bpWriteScalarProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  exact ⟨⟨by omega, lt_of_le_of_lt hcond.2 hnc_w⟩, trivial⟩

/-- Memory history admissibility for `bpReadBktMetaProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpReadBktMetaProg {w : ℕ} {ctx : BpMetaCtx} {b slot : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadBktMetaProg (ctx, (b, slot)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd1 hd2 hd3 hd4 hfr
  subst hwv
  unfold bpReadBktMetaProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen ⟨16 * m, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `bpWriteBktMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteBktMetaProg {w : ℕ} {ctx : BpMetaCtx} {b slot val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteBktMetaProg ((ctx, (b, slot)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd1 hd2 hd3 hd4 hfr
  subst hwv
  unfold bpWriteBktMetaProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf ⟨16 * m, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `bpReadSlabOfProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpReadSlabOfProg {w : ℕ} {ctx : BpMetaCtx} {b v : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadSlabOfProg (ctx, (b, v)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd2 hd3 hd4 hfr
  subst hwv
  unfold bpReadSlabOfProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen
    ⟨m * ms, hw, rfl, hpb, slab_idx_lt hcond.1 hcond.2, by omega⟩

/-- Memory history admissibility for `bpWriteSlabOfProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteSlabOfProg {w : ℕ} {ctx : BpMetaCtx} {b v val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteSlabOfProg ((ctx, (b, v)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd2 hd3 hd4 hfr
  subst hwv
  unfold bpWriteSlabOfProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf
    ⟨m * ms, hw, rfl, hpb, slab_idx_lt hcond.1 hcond.2.1, by omega⟩

/-- Memory history admissibility for `bpReadTailDirRawProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpReadTailDirRawProg {w : ℕ} {ctx : BpMetaCtx} {idx : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadTailDirRawProg (ctx, idx))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd3 hd4 hfr
  subst hwv
  unfold bpReadTailDirRawProg
  refine validHistory_ite (fun hidx => ?_) (fun _ => trivial)
  exact validHistory_readPackedCompGen ⟨8 * m * k, hw, rfl, hpb, hidx, by omega⟩

/-- Memory history admissibility for `bpWriteTailDirRawProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteTailDirRawProg {w : ℕ} {ctx : BpMetaCtx} {idx val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteTailDirRawProg ((ctx, idx), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd3 hd4 hfr
  subst hwv
  unfold bpWriteTailDirRawProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  exact validHistory_writePackedCompGen hwf ⟨8 * m * k, hw, rfl, hpb, hcond.1, by omega⟩

/-- Memory history admissibility for `bpReadSlabOwnerProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpReadSlabOwnerProg {w : ℕ} {ctx : BpMetaCtx} {P lane : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadSlabOwnerProg (ctx, (P, lane)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd4 hfr
  subst hwv
  unfold bpReadSlabOwnerProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen ⟨4 * mbk, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `bpWriteSlabOwnerProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteSlabOwnerProg {w : ℕ} {ctx : BpMetaCtx} {P lane val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteSlabOwnerProg ((ctx, (P, lane)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have hd4 := hv.offTailOwner_ge
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb hd4 hfr
  subst hwv
  unfold bpWriteSlabOwnerProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf ⟨4 * mbk, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `bpReadTailOwnerProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpReadTailOwnerProg {w : ℕ} {ctx : BpMetaCtx} {t isRing : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadTailOwnerProg (ctx, (t, isRing)))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have h16le := hv.sixteen_MK_le_maxTail
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb h16le hfr
  subst hwv
  unfold bpReadTailOwnerProg
  refine validHistory_ite (fun ht => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_readPackedCompGen
    ⟨16 * mt, hw, rfl, hpb, tailOwner_idx_lt h16le ht isRing, hfr⟩

/-- Memory history admissibility for `bpWriteTailOwnerProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpWriteTailOwnerProg {w : ℕ} {ctx : BpMetaCtx} {t isRing val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteTailOwnerProg ((ctx, (t, isRing)), val))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hv.w_mach_pos
  have hwv := hv.w_eq
  have hpb := hv.ptrB_le
  have h16le := hv.sixteen_MK_le_maxTail
  have hfr := hv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hwv hpb h16le hfr
  subst hwv
  unfold bpWriteTailOwnerProg
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf
    ⟨16 * mt, hw, rfl, hpb, tailOwner_idx_lt h16le hcond.1 isRing, hfr⟩

/-- Unconditional memory history admissibility for `bpBlkSlotProg` (pure arithmetic). -/
theorem validHistory_bpBlkSlotProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpBlkSlotProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpBlkSlotProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `bpTbSlotProg` (pure arithmetic). -/
theorem validHistory_bpTbSlotProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpTbSlotProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpTbSlotProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `bpTailRingIdxProg` (pure arithmetic). -/
theorem validHistory_bpTailRingIdxProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpTailRingIdxProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpTailRingIdxProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `bpRingAddProg` (pure arithmetic). -/
theorem validHistory_bpRingAddProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpRingAddProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpRingAddProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `bpRingDiffProg` (pure arithmetic). -/
theorem validHistory_bpRingDiffProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpRingDiffProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpRingDiffProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Unconditional memory history admissibility for `bpBktLocProg` (pure arithmetic). -/
theorem validHistory_bpBktLocProg (w : ℕ) (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpBktLocProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold bpBktLocProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `bpReadBktCountProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpReadBktCountProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadBktCountProg (ctx, b))) := by
  unfold bpReadBktCountProg
  refine validHistory_bp_ro hv (validHistory_bpReadBktMetaProg hv) fun _ _ hv₁ => ?_
  exact validHistory_bp_ro hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ _ =>
    validHistory_bpBktLocProg w _ _

/-- Unconditional memory history admissibility for `bpDivModKProg` (pure arithmetic). -/
theorem validHistory_bpDivModKProg (w : ℕ) (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpDivModKProg x)) := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, _⟩
  trivial

/-- Memory history admissibility for `bpActCurProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpActCurProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActCurProg (ctx, b))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  unfold bpActCurProg
  refine validHistory_bp_ro hv (validHistory_bpReadBktMetaProg hv) fun _ _ _ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `bpEffBlkProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpEffBlkProg {w : ℕ} {ctx : BpMetaCtx} {P off : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpEffBlkProg (ctx, (P, off)))) := by
  unfold bpEffBlkProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bp_ro hv₂ (validHistory_bpReadScalarProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpReadScalarProg hv₃) fun _ _ _ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `bpPhysOfTailProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpPhysOfTailProg {w : ℕ} {ctx : BpMetaCtx} {tIdx : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPhysOfTailProg (ctx, tIdx))) := by
  rcases ctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  unfold bpPhysOfTailProg
  simp only [pure_bind]
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bp_ro hv (validHistory_bpReadTailDirRawProg hv) fun _ _ hv₁ => ?_
  exact validHistory_bp_ro hv₁ (validHistory_bpEffBlkProg hv₁) fun _ _ _ =>
    validHistory_bpBlkSlotProg w _ _

/-- Memory history admissibility for `bpToPhysRemProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpToPhysRemProg {w : ℕ} {ctx : BpMetaCtx} {b k_rem : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpToPhysRemProg (ctx, (b, k_rem)))) := by
  unfold bpToPhysRemProg
  refine validHistory_bp_ro hv (validHistory_bpActCurProg hv) fun _ _ hv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bp_ro hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hv₂ => ?_
    exact validHistory_bp_ro hv₂ (validHistory_bpEffBlkProg hv₂) fun _ _ _ =>
      validHistory_bpBlkSlotProg w _ _
  · refine validHistory_bp_ro hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hv₂ => ?_
    refine validHistory_bp_ro hv₂ (validHistory_bpRingAddProg w _ _) fun _ _ hv₃ => ?_
    refine validHistory_bp_ro hv₃ (validHistory_bpTailRingIdxProg w _ _) fun _ _ hv₄ => ?_
    exact validHistory_bp_ro hv₄ (validHistory_bpReadTailDirRawProg hv₄) fun _ _ hv₅ =>
      validHistory_bpPhysOfTailProg hv₅

/-- Memory history admissibility for `bpToPhysProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpToPhysProg {w : ℕ} {ctx : BpMetaCtx} {b loc : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpToPhysProg (ctx, (b, loc)))) := by
  unfold bpToPhysProg
  refine validHistory_bp_ro hv (validHistory_bpReadBktMetaProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpBktLocProg w _ _) fun _ _ hv₂ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bp_ro hv₂ (validHistory_bpDivModKProg w _ _) fun _ _ hv₃ => ?_
    refine validHistory_bp_ro hv₃ (validHistory_bpReadSlabOfProg hv₃) fun _ _ hv₄ => ?_
    exact validHistory_bp_ro hv₄ (validHistory_bpEffBlkProg hv₄) fun _ _ _ =>
      validHistory_bpBlkSlotProg w _ _
  · simp only [pure_bind]
    exact validHistory_bpToPhysRemProg hv₂

/-- Memory history admissibility for `bpOwnerOfTailProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpOwnerOfTailProg {w : ℕ} {ctx : BpMetaCtx} {tIdx : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpOwnerOfTailProg (ctx, tIdx))) := by
  unfold bpOwnerOfTailProg
  refine validHistory_bp_ro hv (validHistory_bpReadTailOwnerProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadTailOwnerProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpReadBktMetaProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_bp_ro hv₄ (validHistory_bpRingDiffProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpBktLocProg w _ _) fun _ _ _ => trivial

/-- Memory history admissibility for `bpOwnerOfNonSlabProg` under `BpMetaLayout.Valid`
(read-only). -/
theorem validHistory_bpOwnerOfNonSlabProg {w : ℕ} {ctx : BpMetaCtx} {P off tag : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpOwnerOfNonSlabProg (ctx, ((P, off), tag)))) := by
  unfold bpOwnerOfNonSlabProg
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bp_ro hv (validHistory_bpReadSlabOwnerProg hv) fun _ _ hv₁ => ?_
    refine validHistory_bp_ro hv₁ (validHistory_bpActCurProg hv₁) fun _ _ hv₂ => ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
    · refine validHistory_bp_ro hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ _ => ?_
      exact validHistory_bind_ro (validHistory_bpBktLocProg w _ _) fun _ _ _ => trivial
    · refine validHistory_bp_ro hv₂ (validHistory_bpReadSlabOwnerProg hv₂) fun _ _ hv₃ => ?_
      exact validHistory_bp_ro hv₃ (validHistory_bpTbSlotProg w _ _) fun _ _ hv₄ =>
        validHistory_bpOwnerOfTailProg hv₄
  · refine validHistory_bp_ro hv (validHistory_bpReadSlabOwnerProg hv) fun _ _ hv₁ => ?_
    exact validHistory_bp_ro hv₁ (validHistory_bpTbSlotProg w _ _) fun _ _ hv₂ =>
      validHistory_bpOwnerOfTailProg hv₂

/-- Memory history admissibility for `bpOwnerOfProg` under `BpMetaLayout.Valid` (read-only). -/
theorem validHistory_bpOwnerOfProg {w : ℕ} {ctx : BpMetaCtx} {p : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpOwnerOfProg (ctx, p))) := by
  unfold bpOwnerOfProg
  refine validHistory_bp_ro hv (validHistory_bpDivModKProg w _ _) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpEffBlkProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadSlabOwnerProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_bpOwnerOfNonSlabProg hv₃)
  refine validHistory_bp_ro hv₃ (validHistory_bpReadSlabOwnerProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_bp_ro hv₄ (validHistory_bpReadSlabOwnerProg hv₄) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpBktLocProg w _ _) fun _ _ _ => trivial

/-! ## Section 4: `LargeBlockPoolStepProg` `ValidHistory` Proofs -/

private theorem validHistory_bpGetMKProg (w : ℕ) (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpGetMKProg ctx)) := by
  rcases ctx with ⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩; trivial

private theorem validHistory_bpGetCapsProg (w : ℕ) (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpGetCapsProg ctx)) := by
  rcases ctx with ⟨_, ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩; trivial

private theorem validHistory_bpSubProg (w : ℕ) (xy : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpSubProg xy)) := by
  rcases xy with ⟨_, _⟩
  unfold bpSubProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_bpWriteTailRingProg {w : ℕ} {ctx : BpMetaCtx} {b rk val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteTailRingProg ((ctx, (b, rk)), val))) := by
  unfold bpWriteTailRingProg
  exact validHistory_bp_wf hwf hv (validHistory_bpTailRingIdxProg w _ _) fun _ _ hwf₁ hv₁ =>
    validHistory_bpWriteTailDirRawProg hwf₁ hv₁

private theorem validHistory_bpWriteFreeTbStackProg {w : ℕ} {ctx : BpMetaCtx} {i val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteFreeTbStackProg ((ctx, i), val))) := by
  unfold bpWriteFreeTbStackProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bpWriteTailDirRawProg hwf₁ hv₁

private theorem validHistory_bpWriteTbPhysBlkProg {w : ℕ} {ctx : BpMetaCtx} {tb val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteTbPhysBlkProg ((ctx, tb), val))) := by
  unfold bpWriteTbPhysBlkProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bpWriteTailDirRawProg hwf₁ hv₁

private theorem validHistory_bpReadTailInfoProg {w : ℕ} {ctx : BpMetaCtx} {t : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadTailInfoProg (ctx, t))) := by
  unfold bpReadTailInfoProg
  refine validHistory_bp_ro hv (validHistory_bpPhysOfTailProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadTailOwnerProg hv₁) fun _ _ hv₂ => ?_
  exact validHistory_bind_ro (validHistory_bpReadTailOwnerProg hv₂) fun _ _ _ => trivial

private theorem validHistory_bpSwapTailWriteProg {w : ℕ} {ctx : BpMetaCtx}
    {t₁ t₂ b₁ rk₁ b₂ rk₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bpSwapTailWriteProg ((ctx, (t₁, t₂)), ((b₁, rk₁), (b₂, rk₂))))) := by
  unfold bpSwapTailWriteProg
  refine validHistory_bp_wf hwf hv (validHistory_bpWriteTailRingProg hwf hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteTailRingProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteTailOwnerProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteTailOwnerProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteTailOwnerProg hwf₄ hv₄)
    fun _ _ hwf₅ hv₅ => ?_
  exact validHistory_bpWriteTailOwnerProg hwf₅ hv₅

private theorem validHistory_bpSwapTailMetaProg {w : ℕ} {ctx : BpMetaCtx} {t₁ t₂ : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpSwapTailMetaProg (ctx, (t₁, t₂)))) := by
  unfold bpSwapTailMetaProg
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bp_wf hwf hv (validHistory_bpReadTailInfoProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadTailInfoProg hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  exact validHistory_bind_wf hwf₂ (validHistory_bpSwapTailWriteProg hwf₂ hv₂) fun _ _ _ _ => trivial

private theorem validHistory_bpUnresRemoveAtProg {w : ℕ} {ctx : BpMetaCtx} {idx : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpUnresRemoveAtProg (ctx, idx))) := by
  unfold bpUnresRemoveAtProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadSlabOwnerProg hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteScalarProg hv₃) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteSlabOwnerProg hwf₄ hv₄)
    fun _ _ hwf₅ hv₅ => ?_
  exact validHistory_ite (fun _ => validHistory_bpWriteSlabOwnerProg hwf₅ hv₅) fun _ => trivial

private theorem validHistory_bpUnresPushProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpUnresPushProg (ctx, P))) := by
  unfold bpUnresPushProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetCapsProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteSlabOwnerProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteSlabOwnerProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteSlabOwnerProg hwf₄ hv₄)
    fun _ _ _ hv₅ => ?_
  simp only [pure_bind]
  exact validHistory_bpWriteScalarProg hv₅

private theorem validHistory_bpFreeTbProg {w : ℕ} {ctx : BpMetaCtx} {tb : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpFreeTbProg (ctx, tb))) := by
  unfold bpFreeTbProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetCapsProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteFreeTbStackProg hwf₂ hv₂)
    fun _ _ _ hv₃ => ?_
  simp only [pure_bind]
  exact validHistory_bpWriteScalarProg hv₃

private theorem validHistory_bpAllocTbPopProg {w : ℕ} {ctx : BpMetaCtx} {P top' : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAllocTbPopProg (ctx, (P, top')))) := by
  unfold bpAllocTbPopProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadTailDirRawProg hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteSlabOwnerProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  exact validHistory_bpWriteTbPhysBlkProg hwf₄ hv₄

private theorem validHistory_bpAllocTbFreshProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAllocTbFreshProg (ctx, P))) := by
  unfold bpAllocTbFreshProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetCapsProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteSlabOwnerProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  exact validHistory_bpWriteTbPhysBlkProg hwf₄ hv₄

private theorem validHistory_bpAllocTbForProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAllocTbForProg (ctx, P))) := by
  unfold bpAllocTbForProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  exact validHistory_ite (fun _ => validHistory_bpAllocTbPopProg hwf₁ hv₁)
    fun _ => validHistory_bpAllocTbFreshProg hwf₁ hv₁

private theorem validHistory_bpReadPromHdrProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadPromHdrProg ctx)) := by
  unfold bpReadPromHdrProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpDivModKProg w _ _) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadScalarProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpReadScalarProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_bp_ro hv₄ (validHistory_bpReadScalarProg hv₄) fun _ _ hv₅ => ?_
  exact validHistory_bind_ro (validHistory_bpReadScalarProg hv₅) fun _ _ _ => trivial

private theorem validHistory_bpCheckPromCandProg {w : ℕ} {ctx : BpMetaCtx} {i : ℕ}
    {hdr : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCheckPromCandProg ((ctx, i), hdr))) := by
  rcases hdr with ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold bpCheckPromCandProg
  refine validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hv) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_bpFindPromoteIdxProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpFindPromoteIdxProg ctx)) := by
  unfold bpFindPromoteIdxProg
  refine validHistory_bp_ro hv (validHistory_bpReadPromHdrProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpCheckPromCandProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpCheckPromCandProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpCheckPromCandProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bind_ro (validHistory_bpCheckPromCandProg hv₄) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_bpFindTopSwapIdxProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpFindTopSwapIdxProg ctx)) := by
  unfold bpFindTopSwapIdxProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpDivModKProg w _ _) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadScalarProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpReadSlabOwnerProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hv₄) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_bpStartPromoteProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpStartPromoteProg (ctx, b))) := by
  unfold bpStartPromoteProg
  refine validHistory_bp_wf hwf hv (validHistory_bpFindPromoteIdxProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadSlabOwnerProg hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpUnresRemoveAtProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteSlabOwnerProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteSlabOwnerProg hwf₄ hv₄)
    fun _ _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅ (validHistory_bpWriteBktMetaProg hwf₅ hv₅)
    fun _ _ hwf₆ hv₆ => ?_
  exact validHistory_bpWriteBktMetaProg hwf₆ hv₆

private theorem validHistory_bpStartDemoteReadProg {w : ℕ} {ctx : BpMetaCtx} {b vp : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpStartDemoteReadProg (ctx, (b, vp)))) := by
  unfold bpStartDemoteReadProg
  refine validHistory_bp_ro hv (validHistory_bpGetMKProg w ctx s) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadSlabOfProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpRingAddProg w _ _) fun _ _ _ => trivial

private theorem validHistory_bpStartDemoteWriteAProg {w : ℕ} {ctx : BpMetaCtx}
    {b P_act vp r_b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bpStartDemoteWriteAProg ((ctx, b), (P_act, (vp, r_b))))) := by
  unfold bpStartDemoteWriteAProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpAllocTbForProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteBktMetaProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  simp only [pure_bind]
  exact validHistory_bpWriteBktMetaProg hwf₃ hv₃

private theorem validHistory_bpStartDemoteWriteBProg {w : ℕ} {ctx : BpMetaCtx}
    {b P_act hd_new : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bpStartDemoteWriteBProg ((ctx, b), (P_act, hd_new)))) := by
  unfold bpStartDemoteWriteBProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteBktMetaProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteBktMetaProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteBktMetaProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteSlabOwnerProg hwf₄ hv₄)
    fun _ _ hwf₅ hv₅ => ?_
  exact validHistory_bpWriteSlabOwnerProg hwf₅ hv₅

private theorem validHistory_bpStartDemoteProg {w : ℕ} {ctx : BpMetaCtx} {b q_b r_b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpStartDemoteProg (ctx, (b, (q_b, r_b))))) := by
  unfold bpStartDemoteProg
  refine validHistory_bp_wf hwf hv (validHistory_bpSubProg w _ _) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpStartDemoteReadProg hv₁)
    fun ph _ hwf₂ hv₂ => ?_
  rcases ph with ⟨pAct, hdNew⟩
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpStartDemoteWriteAProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpStartDemoteWriteBProg (P_act := pAct) (hd_new := hdNew) hwf₃ hv₃

private theorem validHistory_bpMaybeStartTryDemoteProg {w : ℕ} {ctx : BpMetaCtx} {b q_b r_b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpMaybeStartTryDemoteProg (ctx, (b, (q_b, r_b))))) := by
  unfold bpMaybeStartTryDemoteProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  exact validHistory_ite (fun _ => validHistory_bpStartDemoteProg hwf₁ hv₁) fun _ => trivial

private theorem validHistory_bpMaybeStartIdleProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpMaybeStartIdleProg (ctx, b))) := by
  unfold bpMaybeStartIdleProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpGetCapsProg w ctx _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpReadBktMetaProg hv₃) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpReadScalarProg hv₄) fun _ _ hwf₅ hv₅ => ?_
  exact validHistory_ite (fun _ => validHistory_bpStartPromoteProg hwf₅ hv₅)
    fun _ => validHistory_bpMaybeStartTryDemoteProg hwf₅ hv₅

private theorem validHistory_bpMaybeStartMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpMaybeStartMetaProg (ctx, b))) := by
  unfold bpMaybeStartMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadBktMetaProg hv) fun _ _ hwf₁ hv₁ => ?_
  exact validHistory_ite (fun _ => trivial) fun _ => validHistory_bpMaybeStartIdleProg hwf₁ hv₁

private theorem validHistory_bpActPromCoordsProg {w : ℕ} {ctx : BpMetaCtx} {b cur : ℕ}
    {s : Memory.State} (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromCoordsProg ((ctx, b), cur))) := by
  unfold bpActPromCoordsProg
  refine validHistory_bp_ro hv (validHistory_bpReadBktMetaProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadSlabOwnerProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpRingAddProg w _ _) fun _ _ hv₄ => ?_
  refine validHistory_bp_ro hv₄ (validHistory_bpTailRingIdxProg w _ _) fun _ _ hv₅ => ?_
  refine validHistory_bp_ro hv₅ (validHistory_bpReadTailDirRawProg hv₅) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpTbSlotProg w _ _) fun _ _ _ => trivial

private theorem validHistory_bpActPromFinAProg {w : ℕ} {ctx : BpMetaCtx} {b P_act : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromFinAProg ((ctx, b), P_act))) := by
  unfold bpActPromFinAProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetCapsProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadSlabOwnerProg hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpFreeTbProg hwf₃ hv₃) fun _ _ hwf₄ hv₄ => ?_
  simp only [pure_bind]
  exact validHistory_bind_wf hwf₄ (validHistory_bpWriteBktMetaProg hwf₄ hv₄) fun _ _ _ _ => trivial

private theorem validHistory_bpActPromFinCProg {w : ℕ} {ctx : BpMetaCtx} {b P_act vp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromFinCProg ((ctx, b), (P_act, vp)))) := by
  unfold bpActPromFinCProg
  refine validHistory_bp_wf hwf hv (validHistory_bpWriteBktMetaProg hwf hv)
    fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteSlabOfProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteSlabOwnerProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpWriteSlabOwnerProg hwf₃ hv₃

private theorem validHistory_bpActPromFinBProg {w : ℕ} {ctx : BpMetaCtx} {b P_act vp : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromFinBProg ((ctx, b), (P_act, vp)))) := by
  unfold bpActPromFinBProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpRingAddProg w _ _) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpSubProg w _ _) fun _ _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅ (validHistory_bpWriteBktMetaProg hwf₅ hv₅)
    fun _ _ hwf₆ hv₆ => ?_
  refine validHistory_bp_wf hwf₆ hv₆ (validHistory_bpWriteBktMetaProg hwf₆ hv₆)
    fun _ _ hwf₇ hv₇ => ?_
  exact validHistory_bpActPromFinCProg hwf₇ hv₇

private theorem validHistory_bpActPromoteRunProg {w : ℕ} {ctx : BpMetaCtx} {b ac : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromoteRunProg ((ctx, b), ac))) := by
  unfold bpActPromoteRunProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpActPromCoordsProg hv₂)
    fun coords _ hwf₃ hv₃ => ?_
  rcases coords with ⟨pAct, ⟨tCur, tAct⟩⟩
  refine validHistory_bp_wf hwf₃ hv₃
    (validHistory_bpSwapTailMetaProg (t₁ := tCur) (t₂ := tAct) hwf₃ hv₃) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    exact validHistory_bind_wf hwf₄ (validHistory_bpWriteBktMetaProg hwf₄ hv₄)
      fun _ _ _ _ => trivial
  · refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpActPromFinAProg (P_act := pAct) hwf₄ hv₄)
      fun _ _ hwf₅ hv₅ => ?_
    exact validHistory_bind_wf hwf₅ (validHistory_bpActPromFinBProg hwf₅ hv₅)
      fun _ _ _ _ => trivial

private theorem validHistory_bpActPromoteStepProg {w : ℕ} {ctx : BpMetaCtx} {b ac : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActPromoteStepProg ((ctx, b), ac))) := by
  unfold bpActPromoteStepProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadBktMetaProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  exact validHistory_ite (fun _ => trivial) fun _ => validHistory_bpActPromoteRunProg hwf₂ hv₂

private theorem validHistory_bpActDemoteBaseProg {w : ℕ} {ctx : BpMetaCtx} {b cur' : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActDemoteBaseProg ((ctx, b), cur'))) := by
  unfold bpActDemoteBaseProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadBktMetaProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadSlabOwnerProg hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpRingAddProg w _ _) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpTbSlotProg w _ _) fun _ _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅ (validHistory_bpWriteTailRingProg hwf₅ hv₅)
    fun _ _ hwf₆ hv₆ => ?_
  refine validHistory_bp_wf hwf₆ hv₆ (validHistory_bpWriteTailOwnerProg hwf₆ hv₆)
    fun _ _ hwf₇ hv₇ => ?_
  exact validHistory_bind_wf hwf₇ (validHistory_bpWriteTailOwnerProg hwf₇ hv₇)
    fun _ _ _ _ => trivial

private theorem validHistory_bpActDemoteStepProg {w : ℕ} {ctx : BpMetaCtx} {b ac : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActDemoteStepProg ((ctx, b), ac))) := by
  unfold bpActDemoteStepProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpSubProg w _ _) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpActDemoteBaseProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpSubProg w _ _) fun _ _ hwf₅ hv₅ => ?_
    exact validHistory_bind_wf hwf₅ (validHistory_bpWriteBktMetaProg hwf₅ hv₅)
      fun _ _ _ _ => trivial
  · refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpUnresPushProg hwf₄ hv₄)
      fun _ _ hwf₅ hv₅ => ?_
    exact validHistory_bind_wf hwf₅ (validHistory_bpWriteBktMetaProg hwf₅ hv₅)
      fun _ _ _ _ => trivial

private theorem validHistory_bpActStepMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpActStepMetaProg (ctx, b))) := by
  unfold bpActStepMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  exact validHistory_ite (fun _ => validHistory_bpActPromoteStepProg hwf₂ hv₂)
    fun _ => validHistory_bpActDemoteStepProg hwf₂ hv₂

/-- Memory history admissibility for `bpBktTickMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpBktTickMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpBktTickMetaProg (ctx, b))) := by
  unfold bpBktTickMetaProg
  exact validHistory_bp_wf hwf hv (validHistory_bpMaybeStartMetaProg hwf hv) fun _ _ hwf₁ hv₁ =>
    validHistory_bpActStepMetaProg hwf₁ hv₁

private theorem validHistory_bpCommitTopSwapReadProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitTopSwapReadProg ctx)) := by
  unfold bpCommitTopSwapReadProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadSlabOwnerProg hv₂) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpReadSlabOwnerProg hv₃) fun _ _ hv₄ => ?_
  refine validHistory_bp_ro hv₄ (validHistory_bpReadSlabOwnerProg hv₄) fun _ _ hv₅ => ?_
  refine validHistory_bp_ro hv₅ (validHistory_bpReadSlabOwnerProg hv₅) fun _ _ hv₆ => ?_
  exact validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hv₆) fun _ _ _ => trivial

private theorem validHistory_bpCommitTopSwapBaseAProg {w : ℕ} {ctx : BpMetaCtx} {S D tagS : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitTopSwapBaseAProg (ctx, ((S, D), tagS)))) := by
  unfold bpCommitTopSwapBaseAProg
  refine validHistory_bp_wf hwf hv (validHistory_bpWriteScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteScalarProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteSlabOwnerProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpWriteSlabOwnerProg hwf₃ hv₃

private theorem validHistory_bpCommitTopSwapBaseBProg {w : ℕ} {ctx : BpMetaCtx}
    {S D m1S m2S posD tbD : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bpCommitTopSwapBaseBProg (ctx, ((S, D), ((m1S, m2S), (posD, tbD)))))) := by
  unfold bpCommitTopSwapBaseBProg
  refine validHistory_bp_wf hwf hv (validHistory_bpWriteSlabOwnerProg hwf hv)
    fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteSlabOwnerProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteSlabOwnerProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpWriteSlabOwnerProg hwf₃ hv₃

private theorem validHistory_bpCommitTopSwapPtrsProg {w : ℕ} {ctx : BpMetaCtx}
    {info : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitTopSwapPtrsProg (ctx, info))) := by
  rcases info with ⟨⟨S, D⟩, ⟨⟨tagS, m1S⟩, ⟨m2S, ⟨posD, tbD⟩⟩⟩⟩
  unfold bpCommitTopSwapPtrsProg
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bp_wf hwf hv (validHistory_bpWriteSlabOwnerProg hwf hv)
      fun _ _ hwf₁ hv₁ => ?_
    refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteSlabOwnerProg hwf₁ hv₁)
      fun _ _ hwf₂ hv₂ => ?_
    refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteTbPhysBlkProg hwf₂ hv₂)
      fun _ _ hwf₃ hv₃ => ?_
    exact validHistory_bpWriteTbPhysBlkProg hwf₃ hv₃
  · refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
    · refine validHistory_bp_wf hwf hv (validHistory_bpWriteSlabOfProg hwf hv)
        fun _ _ hwf₁ hv₁ => ?_
      refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteSlabOwnerProg hwf₁ hv₁)
        fun _ _ hwf₂ hv₂ => ?_
      exact validHistory_bpWriteTbPhysBlkProg hwf₂ hv₂
    · refine validHistory_bp_wf hwf hv (validHistory_bpWriteBktMetaProg hwf hv)
        fun _ _ hwf₁ hv₁ => ?_
      refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpWriteSlabOwnerProg hwf₁ hv₁)
        fun _ _ hwf₂ hv₂ => ?_
      refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteTbPhysBlkProg hwf₂ hv₂)
        fun _ _ hwf₃ hv₃ => ?_
      exact validHistory_bpWriteTbPhysBlkProg hwf₃ hv₃

private theorem validHistory_bpCommitTopSwapMetaProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitTopSwapMetaProg ctx)) := by
  unfold bpCommitTopSwapMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpCommitTopSwapReadProg hv)
    fun info _ hwf₁ hv₁ => ?_
  rcases info with ⟨⟨S, D⟩, ⟨⟨tagS, m1S⟩, ⟨m2S, ⟨posD, tbD⟩⟩⟩⟩
  refine validHistory_bp_wf hwf₁ hv₁
    (validHistory_bpCommitTopSwapBaseAProg (S := S) (D := D) (tagS := tagS) hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂
    (validHistory_bpCommitTopSwapBaseBProg
      (S := S) (D := D) (m1S := m1S) (m2S := m2S) (posD := posD) (tbD := tbD) hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpCommitTopSwapPtrsProg hwf₃ hv₃

private theorem validHistory_bpTopSwapReadSwProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopSwapReadSwProg ctx)) := by
  unfold bpTopSwapReadSwProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadScalarProg hv₂) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_bpBlkSlotProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpBlkSlotProg w _ _) fun _ _ _ => trivial

private theorem validHistory_bpTopSwapStepMetaProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopSwapStepMetaProg ctx)) := by
  unfold bpTopSwapStepMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpGetMKProg w ctx _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpTopSwapReadSwProg hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_bind_wf hwf₃ (validHistory_bpWriteScalarProg hv₃) fun _ _ _ _ => trivial
  · exact validHistory_bind_wf hwf₃ (validHistory_bpCommitTopSwapMetaProg hwf₃ hv₃)
      fun _ _ _ _ => trivial

private theorem validHistory_bpTopCleanActProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopCleanActProg (ctx, P))) := by
  unfold bpTopCleanActProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadSlabOwnerProg hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_ite (fun _ => validHistory_bpTopSwapStepMetaProg hwf₃ hv₃) fun _ => trivial

private theorem validHistory_bpStartTopSwapProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpStartTopSwapProg (ctx, P))) := by
  unfold bpStartTopSwapProg
  refine validHistory_bp_wf hwf hv (validHistory_bpFindTopSwapIdxProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadSlabOwnerProg hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteScalarProg hv₃) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteScalarProg hv₄) fun _ _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅ (validHistory_bpWriteScalarProg hv₅) fun _ _ hwf₆ hv₆ => ?_
  exact validHistory_bpTopSwapStepMetaProg hwf₆ hv₆

private theorem validHistory_bpTopCleanIdleProg {w : ℕ} {ctx : BpMetaCtx} {P : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopCleanIdleProg (ctx, P))) := by
  unfold bpTopCleanIdleProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadSlabOwnerProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadSlabOwnerProg hv₁)
      fun _ _ hwf₂ hv₂ => validHistory_bpActStepMetaProg hwf₂ hv₂
  · refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpReadScalarProg hv₁)
      fun _ _ hwf₂ hv₂ => ?_
    exact validHistory_ite (fun _ => validHistory_bpStartTopSwapProg hwf₂ hv₂) fun _ => trivial

/-- Memory history admissibility for `bpTopCleanMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpTopCleanMetaProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopCleanMetaProg ctx)) := by
  unfold bpTopCleanMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpDivModKProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_ite (fun _ => validHistory_bpTopCleanActProg hwf₃ hv₃)
    fun _ => validHistory_bpTopCleanIdleProg hwf₃ hv₃

private theorem validHistory_bpAppendReadTopProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAppendReadTopProg ctx)) := by
  unfold bpAppendReadTopProg
  refine validHistory_bp_ro hv (validHistory_bpReadScalarProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpDivModKProg w _ _) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpReadSlabOwnerProg hv₂) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_bpTbSlotProg w _ _) fun _ _ _ => trivial

private theorem validHistory_bpAppendWriteBaseProg {w : ℕ} {ctx : BpMetaCtx}
    {b ns r_b t_new rk_new : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bpAppendWriteBaseProg ((ctx, b), ((ns, r_b), (t_new, rk_new))))) := by
  unfold bpAppendWriteBaseProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpGetCapsProg w ctx _) fun _ _ hwf₂ hv₂ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpWriteBktMetaProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpWriteTailRingProg hwf₄ hv₄)
    fun _ _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅ (validHistory_bpWriteTailOwnerProg hwf₅ hv₅)
    fun _ _ hwf₆ hv₆ => ?_
  exact validHistory_bpWriteTailOwnerProg hwf₆ hv₆

private theorem validHistory_bpAdvanceTopBlkProg {w : ℕ} {ctx : BpMetaCtx} {bf : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAdvanceTopBlkProg (ctx, bf))) := by
  unfold bpAdvanceTopBlkProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetCapsProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpUnresPushProg hwf₁ hv₁)
    fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpAllocTbForProg hwf₂ hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpWriteSlabOwnerProg hwf₃ hv₃

/-- Memory history admissibility for `bpRawPostAppendMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpRawPostAppendMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRawPostAppendMetaProg (ctx, b))) := by
  unfold bpRawPostAppendMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpGetMKProg w ctx s) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpAppendReadTopProg hv₁)
    fun top _ hwf₂ hv₂ => ?_
  rcases top with ⟨⟨ns, ⟨bf, rem⟩⟩, tNew⟩
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadBktMetaProg hv₂) fun r_b _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpReadBktMetaProg hv₃) fun _ _ hwf₄ hv₄ => ?_
  refine validHistory_bp_wf hwf₄ hv₄ (validHistory_bpRingAddProg w _ _) fun rk _ hwf₅ hv₅ => ?_
  refine validHistory_bp_wf hwf₅ hv₅
    (validHistory_bpAppendWriteBaseProg
      (ns := ns) (r_b := r_b) (t_new := tNew) (rk_new := rk) hwf₅ hv₅)
    fun _ _ hwf₆ hv₆ => ?_
  exact validHistory_ite (fun _ => trivial)
    fun _ => validHistory_bpAdvanceTopBlkProg (bf := bf) hwf₆ hv₆

private theorem validHistory_bpPrepPopEndProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPrepPopEndProg (ctx, b))) := by
  unfold bpPrepPopEndProg
  refine validHistory_bp_ro hv (validHistory_bpReadBktMetaProg hv) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadBktMetaProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpSubProg w _ _) fun _ _ hv₃ => ?_
  refine validHistory_bp_ro hv₃ (validHistory_bpRingAddProg w _ _) fun _ _ hv₄ => ?_
  exact validHistory_bp_ro hv₄ (validHistory_bpTailRingIdxProg w _ _) fun _ _ hv₅ =>
    validHistory_bpReadTailDirRawProg hv₅

private theorem validHistory_bpPrepPopTopProg {w : ℕ} {ctx : BpMetaCtx} {s : Memory.State}
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPrepPopTopProg ctx)) := by
  unfold bpPrepPopTopProg
  refine validHistory_bp_ro hv (validHistory_bpGetMKProg w ctx s) fun _ _ hv₁ => ?_
  refine validHistory_bp_ro hv₁ (validHistory_bpReadScalarProg hv₁) fun _ _ hv₂ => ?_
  refine validHistory_bp_ro hv₂ (validHistory_bpDivModKProg w _ _) fun _ _ hv₃ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · exact validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hv₃) fun _ _ _ =>
      validHistory_bpTbSlotProg w _ _
  · refine validHistory_bp_ro hv₃ (validHistory_bpSubProg w _ _) fun _ _ hv₄ => ?_
    exact validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hv₄) fun _ _ _ =>
      validHistory_bpTbSlotProg w _ _

/-- Memory history admissibility for `bpPrepPopMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpPrepPopMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPrepPopMetaProg (ctx, b))) := by
  unfold bpPrepPopMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpPrepPopEndProg hv) fun _ _ hwf₁ hv₁ => ?_
  exact validHistory_bp_wf hwf₁ hv₁ (validHistory_bpPrepPopTopProg hv₁) fun _ _ hwf₂ hv₂ =>
    validHistory_bpSwapTailMetaProg hwf₂ hv₂

private theorem validHistory_bpCommitPopShrinkProg {w : ℕ} {ctx : BpMetaCtx} {b ns r_b : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitPopShrinkProg ((ctx, b), (ns, r_b)))) := by
  unfold bpCommitPopShrinkProg
  refine validHistory_bp_wf hwf hv (validHistory_bpSubProg w _ _) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpWriteScalarProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  exact validHistory_bpWriteBktMetaProg hwf₃ hv₃

private theorem validHistory_bpCommitPopCase2CleanProg {w : ℕ} {ctx : BpMetaCtx} {bf : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitPopCase2CleanProg (ctx, bf))) := by
  unfold bpCommitPopCase2CleanProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadSlabOwnerProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpSubProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadSlabOwnerProg hv₂)
    fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_bp_wf hwf₃ hv₃ (validHistory_bpFreeTbProg hwf₃ hv₃) fun _ _ hwf₄ hv₄ => ?_
  exact validHistory_bpUnresRemoveAtProg hwf₄ hv₄

/-- Memory history admissibility for `bpCommitPopMetaProg` under `Memory.WellFormed` and
`BpMetaLayout.Valid`. -/
theorem validHistory_bpCommitPopMetaProg {w : ℕ} {ctx : BpMetaCtx} {b : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hv : (BpMetaLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpCommitPopMetaProg (ctx, b))) := by
  unfold bpCommitPopMetaProg
  refine validHistory_bp_wf hwf hv (validHistory_bpReadScalarProg hv) fun _ _ hwf₁ hv₁ => ?_
  refine validHistory_bp_wf hwf₁ hv₁ (validHistory_bpDivModKProg w _ _) fun _ _ hwf₂ hv₂ => ?_
  refine validHistory_bp_wf hwf₂ hv₂ (validHistory_bpReadBktMetaProg hv₂) fun _ _ hwf₃ hv₃ => ?_
  refine validHistory_ite (fun _ => validHistory_bpCommitPopShrinkProg hwf₃ hv₃) fun _ => ?_
  exact validHistory_bp_wf hwf₃ hv₃ (validHistory_bpCommitPopCase2CleanProg hwf₃ hv₃)
    fun _ _ hwf₄ hv₄ => validHistory_bpCommitPopShrinkProg hwf₄ hv₄

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
