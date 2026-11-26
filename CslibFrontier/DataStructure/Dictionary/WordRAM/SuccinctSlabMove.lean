/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.WramOmega

/-!
# Slab Promotion Loop in `Memory.Prog`

This module implements the `K`-step (`K = slabSize n_max`) slab promotion (`promoteStepProg`,
`promoteLoopProg`, and `promoteSlabProg`) in `Memory.Prog`, proves that it preserves
`SlotStoreInv`, `bCount`, and all logical `(quotAt, valAt)` entries via `slotOf`, and certifies
its Word-RAM realization via `realize` and `Realizes.iterate₀`. Slab demotion (`demoteSlabProg`)
is implemented in `CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteStepProg`: single step
  `k < slabSize n_max` of slab promotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteLoopProg`: `K`-step iteration of
  `promoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteSlabProg`: complete slab promotion
  (`promoteLoopProg` followed by `gmPushSlabProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.PromoteSlabInv`: entry invariant for
  `promoteSlabProg` (`gm (gmRIdx b) = 2 * slabSize n_max`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteStepProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_promoteStepGen`: single-step invariant
  preservation and `Realizes` certificate for `promoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.promoteSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_promoteSlabGen`: full-slab promotion
  invariant preservation, `O(K)` `memoryCost`, and `Realizes` certificate for `promoteSlabProg`.
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
open Finset

/-! ## Section 1: Single step of slab promotion (`promoteStepProg`) -/

/-- Parameter-free single step `k < slabSize n_max` of slab promotion for
`x = ((dp, (base, b)), k)`. -/
@[expose]
def promoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let dp := x.1.1
  let base := x.1.2.1
  let b := x.1.2.2
  let k := x.2
  let u := dpSlabSizeSubOne dp - k
  let r_top := dpSlabSize dp + u
  let t_u ← readGMGenProg (dp, (base, dpGmTailPtrBase dp + (b * dpTailCap dp + u)))
  let t_top ← readGMGenProg (dp, (base, dpGmTailPtrBase dp + (b * dpTailCap dp + r_top)))
  let p_new ← readGMGenProg (dp, (base, 0))
  let g_u := dpNMaxSubOne dp - t_u
  let g_top := dpNMaxSubOne dp - t_top
  let g_slab := p_new * dpSlabSize dp + k
  let q_u ← readQuotGenProg (dp, (base, g_u))
  let v_u ← readValGenProg (dp, (base, g_u))
  let q_top ← readQuotGenProg (dp, (base, g_top))
  let v_top ← readValGenProg (dp, (base, g_top))
  writeQuotGenProg (dp, ((base, g_u), q_top))
  writeValGenProg (dp, ((base, g_u), v_top))
  removeLastTailItemGenProg (dp, (base, b))
  writeQuotGenProg (dp, ((base, g_slab), q_u))
  let _ ← writeValGenProg (dp, ((base, g_slab), v_u))
  pure (k + 1)

/-- One step `k < slabSize n_max` of slab promotion for `x = ((base, b), k)`:
1. Reads the payload `(q_u, v_u)` at low tail item `u = (slabSize n_max - 1) - k` and the payload
   `(q_top, v_top)` at the last tail item `r_top = slabSize n_max + u = gm (gmRIdx b) - 1`.
2. Copies `(q_top, v_top)` into tail item `u`.
3. Calls `removeLastTailItemProg (base, b)` to compact and remove tail item `r_top`.
4. Writes `(q_u, v_u)` into physical slab slot `gm 0 * slabSize n_max + k` and returns `k + 1`. -/
@[expose]
def promoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  promoteStepGenProg ((mkDictParams U V w n_max h_space, x.1), x.2)

@[simp] theorem promoteStepGenProg_mk (U V w n_max h_space : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ) :
    promoteStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      promoteStepProg U V w n_max h_space (d1, d2) := by
  rfl

@[simp]
theorem memoryCost_promoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (promoteStepProg U V w n_max h_space x) s = 66 := by
  simp [promoteStepProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    promoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk, p_gmTailPtrBase_mk, p_tailCap_mk,
    p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk,
    writeValGenProg_mk, removeLastTailItemGenProg_mk]

theorem one_le_memoryCost_promoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (promoteStepGenProg x) s := by
  simp only [promoteStepGenProg, readGMGenProg, readPackedGenProg, ← PFunctor.FreeM.bind_eq_bind,
    memoryCost_bind, memoryCost_readPackedProg]
  omega

/-- Pure state invariant for step `k` (`k < slabSize n_max`) of `promoteStepProg`. -/
@[expose]
def PromoteStepInv (U V w₀ n_max h_space base b k : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  k < slabSize n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 2 * slabSize n_max - k ∧
  gm 0 * slabSize n_max + k + gm 1 ≤ n_max

/-- Precondition for `promoteStepProg` in `Realizes`. -/
@[expose]
def PromoteStepPre (U V w₀ n_max h_space w base b k : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  PromoteStepInv U V w₀ n_max h_space base b k s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `promoteStepGenProg`. -/
@[expose]
def PromoteStepGenPre (w : ℕ) (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w x.1.1 x.1.2.1 ∧
  PromoteStepInv (dpU x.1.1) (dpV x.1.1) (dpW x.1.1) (dpNMax x.1.1) (dpHSpace x.1.1)
    x.1.2.1 x.1.2.2 x.2 s ∧
  0 < bucketBits (dpNMax x.1.1)

@[simp] theorem promoteStepGenPre_mk (U V w₀ n_max h_space w : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ)
    (s : Memory.State) :
    PromoteStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      PromoteStepPre U V w₀ n_max h_space w d1.1 d1.2 d2 s := Iff.rfl

/-- Execute promotion using only readback and individual state equations. Keeping the five
intermediate states abstract prevents equality checking from evaluating the packed writes or
`removeLastTailItemProg`; the invariant proof supplies their semantic effects separately. -/
private theorem promoteStepProg_exec {U V w n_max h_space base b k : ℕ}
    (s s₁ s₂ s₃ s₄ s₅ : Memory.State)
    (t_u t_top p_new q_u v_u q_top v_top : ℕ)
    (hres_tu : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space
        (base, gmTailPtrBase n_max +
          (b * tailCapPerBucket n_max + (slabSize n_max - 1 - k)))) = t_u)
    (hres_ttop : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space
        (base, gmTailPtrBase n_max +
          (b * tailCapPerBucket n_max + (slabSize n_max + (slabSize n_max - 1 - k))))) = t_top)
    (hres_p : (Memory.spec 0).clientResult s
      (readGMProg U V w n_max h_space (base, 0)) = p_new)
    (hres_qu : (Memory.spec 0).clientResult s
      (readQuotProg U w n_max h_space (base, n_max - 1 - t_u)) = q_u)
    (hres_vu : (Memory.spec 0).clientResult s
      (readValProg U V w n_max h_space (base, n_max - 1 - t_u)) = v_u)
    (hres_qtop : (Memory.spec 0).clientResult s
      (readQuotProg U w n_max h_space (base, n_max - 1 - t_top)) = q_top)
    (hres_vtop : (Memory.spec 0).clientResult s
      (readValProg U V w n_max h_space (base, n_max - 1 - t_top)) = v_top)
    (hs1 : (Memory.spec 0).clientState s
      (writeQuotProg U w n_max h_space ((base, n_max - 1 - t_u), q_top)) = s₁)
    (hs2 : (Memory.spec 0).clientState s₁
      (writeValProg U V w n_max h_space ((base, n_max - 1 - t_u), v_top)) = s₂)
    (hs3 : (Memory.spec 0).clientState s₂
      (removeLastTailItemProg U V w n_max h_space (base, b)) = s₃)
    (hs4 : (Memory.spec 0).clientState s₃
      (writeQuotProg U w n_max h_space ((base, p_new * slabSize n_max + k), q_u)) = s₄)
    (hs5 : (Memory.spec 0).clientState s₄
      (writeValProg U V w n_max h_space ((base, p_new * slabSize n_max + k), v_u)) = s₅) :
    (Memory.spec 0).clientResult s
        (promoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 ∧
    (Memory.spec 0).clientState s
        (promoteStepProg U V w n_max h_space ((base, b), k)) = s₅ := by
  simp only [promoteStepProg, promoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk,
    readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, removeLastTailItemGenProg_mk]
  refine ⟨by simp only [StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientResult_pure], ?_⟩
  rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_tu,
    StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_ttop,
    StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_p,
    StateTransitionSpec.clientState_bind, clientState_readQuotProg, hres_qu,
    StateTransitionSpec.clientState_bind, clientState_readValProg, hres_vu,
    StateTransitionSpec.clientState_bind, clientState_readQuotProg, hres_qtop,
    StateTransitionSpec.clientState_bind, clientState_readValProg, hres_vtop,
    StateTransitionSpec.clientState_bind, hs1,
    StateTransitionSpec.clientState_bind, hs2,
    StateTransitionSpec.clientState_bind, hs3,
    StateTransitionSpec.clientState_bind, hs4,
    StateTransitionSpec.clientState_bind, hs5, StateTransitionSpec.clientState_pure]

/-- Index and capacity bounds for one step of slab promotion, shared by
`promoteStepProg_effect` and `promoteStep_bounds`. -/
private theorem promoteStep_index_bounds {U V w n_max h_space base b k : ℕ}
    {s : Memory.State} (hb_pos : 0 < bucketBits n_max)
    (hpre : PromoteStepInv U V w n_max h_space base b k s) :
    let gm := gmAt base U V w n_max h_space s.mem
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let t_u := gm (gmTailPtrIdx n_max b u)
    let t_top := gm (gmTailPtrIdx n_max b r_top)
    r_top < tailCapPerBucket n_max ∧
    gmTailPtrIdx n_max b u < globalMetaLen n_max ∧
    gmTailPtrIdx n_max b r_top < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    t_u ≤ n_max - 1 ∧
    t_top ≤ n_max - 1 ∧
    (n_max - 1) - t_u < n_max ∧
    (n_max - 1) - t_top < n_max ∧
    gm 0 * slabSize n_max + k < n_max ∧
    1 ≤ gm (gmRIdx b) ∧
    k + 1 ≤ max n_max 1 := by
  rcases hpre with ⟨hb, hk_lt, htail, _, hrb_eq, htot⟩
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hTcap : tailCapPerBucket n_max = 2 * slabSize n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hr_le_nt := r_le_ntails_of_tailBijection htail hb
  have hr_top_cap : slabSize n_max + (slabSize n_max - 1 - k) < tailCapPerBucket n_max := by omega
  have htu_lt := htail.ptr_lt b hb (slabSize n_max - 1 - k) (by omega)
  have httop_lt := htail.ptr_lt b hb (slabSize n_max + (slabSize n_max - 1 - k)) (by omega)
  exact ⟨hr_top_cap, gmTailPtrIdx_lt hb_pos hb (by omega), gmTailPtrIdx_lt hb_pos hb hr_top_cap,
    by wram_omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Under `PromoteStepInv U V w n_max h_space base b k s` (`k < slabSize n_max`,
`gm (gmRIdx b) = 2 * slabSize n_max - k`), `promoteStepProg` returns `k + 1` in `memoryCost = 66`
(`memoryCost_promoteStepProg`). It preserves `frontier`, `lmAt`, and memory outside
`[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It moves tail item
`u = (slabSize n_max - 1) - k` of bucket `b` to physical slab slot `gm 0 * slabSize n_max + k`,
compacts the last tail item `r_top = slabSize n_max + u` into `u`, and updates `gmAt` to
`gmRemoveTail n_max gm b`. -/
theorem promoteStepProg_effect {U V w n_max h_space base b k : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : PromoteStepInv U V w n_max h_space base b k s) :
    let gm := gmAt base U V w n_max h_space s.mem
    let qA := quotAt base U w n_max h_space s.mem
    let vA := valAt base U V w n_max h_space s.mem
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let g_u := (n_max - 1) - gm (gmTailPtrIdx n_max b u)
    let g_top := (n_max - 1) - gm (gmTailPtrIdx n_max b r_top)
    let g_del := (n_max - 1) - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
    let g_last := (n_max - 1) - (gm 1 - 1)
    let g_slab := gm 0 * slabSize n_max + k
    let s' := (Memory.spec 0).clientState s
      (promoteStepProg U V w n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (promoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update
        (Function.update (Function.update qA g_u (qA g_top))
          g_del (Function.update qA g_u (qA g_top) g_last))
        g_slab (qA g_u) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update
        (Function.update (Function.update vA g_u (vA g_top))
          g_del (Function.update vA g_u (vA g_top) g_last))
        g_slab (vA g_u) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmRemoveTail n_max gm b := by
  intro gm qA vA u r_top g_u g_top g_del g_last g_slab s'
  obtain ⟨_, hptr_u_lt, hptr_top_lt, h0_lt, _, _, hgu_lt, hgtop_lt, hgslab_lt, hr_pos, _⟩ :=
    promoteStep_index_bounds hb_pos hpre
  rcases hpre with ⟨hb, _, htail, _, _, _⟩
  set q_u := qA g_u
  set v_u := vA g_u
  set q_top := qA g_top
  set v_top := vA g_top
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hgu_lt (quotAt_lt ..) s
  set s₁ := (Memory.spec 0).clientState s (writeQuotProg U w n_max h_space ((base, g_u), q_top))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hgu_lt (valAt_lt ..) s₁
  set s₂ := (Memory.spec 0).clientState s₁ (writeValProg U V w n_max h_space ((base, g_u), v_top))
  have hgm2 : gmAt base U V w n_max h_space s₂.mem = gm := by rw [hg2, hg1]
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s₂ (by rwa [hgm2]) (by rwa [hgm2])
  set s₃ := (Memory.spec 0).clientState s₂ (removeLastTailItemProg U V w n_max h_space (base, b))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hgslab_lt (quotAt_lt ..) s₃
  set s₄ := (Memory.spec 0).clientState s₃ (writeQuotProg U w n_max h_space ((base, g_slab), q_u))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hgslab_lt (valAt_lt ..) s₄
  set s₅ := (Memory.spec 0).clientState s₄ (writeValProg U V w n_max h_space ((base, g_slab), v_u))
  obtain ⟨hres, hst⟩ :=
    promoteStepProg_exec s s₁ s₂ s₃ s₄ s₅ _ _ _ q_u v_u q_top v_top
      (clientResult_readGMProg s hptr_u_lt) (clientResult_readGMProg s hptr_top_lt)
      (clientResult_readGMProg s h0_lt) (clientResult_readQuotProg s hgu_lt)
      (clientResult_readValProg s hgu_lt) (clientResult_readQuotProg s hgtop_lt)
      (clientResult_readValProg s hgtop_lt) rfl rfl rfl rfl rfl
  change s' = s₅ at hst
  rw [hst]
  refine ⟨hres, by rw [hf5, hf4, hf3, hf2, hf1], fun a ha => ?_,
    by rw [hq5, hq4, hq3, hgm2, hq2, hq1],
    by rw [hv5, hv4, hv3, hgm2, hv2, hv1],
    by rw [hl5, hl4, hl3, hl2, hl1],
    by rw [hg5, hg4, hg3, hgm2]⟩
  have ha_q : ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) := by
    wram_omega [ha]
  have ha_v : ¬(base + offVal U w n_max h_space ≤ a ∧ a < base + offLM U V w n_max h_space) := by
    wram_omega [ha]
  rw [hout5 a ha_v, hout4 a ha_q, hout3 a ha, hout2 a ha_v, hout1 a ha_q]

/-- Bounds for the reads and writes of `promoteStepProg`, stated on the results of its reads,
together with the precondition of its `removeLastTailItemProg` call; shared by
`realizes_promoteStepGen` and `validProg_promoteStep`. -/
private theorem promoteStep_bounds {U V w₀ n_max h_space base b k : ℕ}
    {s : Memory.State} (hw : 0 < w₀)
    (h : PromoteStepInv U V w₀ n_max h_space base b k s ∧ 0 < bucketBits n_max) :
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let ptr_u_idx := gmTailPtrBase n_max + (b * tailCapPerBucket n_max + u)
    let ptr_top_idx := gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_top)
    let t_u := (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (base, ptr_u_idx))
    let s1 := (Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (base, ptr_u_idx))
    let t_top := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (base, ptr_top_idx))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (base, ptr_top_idx))
    let p_new := (Memory.spec 0).clientResult s2 (readGMProg U V w₀ n_max h_space (base, 0))
    let g_u := (n_max - 1) - t_u
    let g_top := (n_max - 1) - t_top
    let g_slab := p_new * slabSize n_max + k
    let q_top := (Memory.spec 0).clientResult s (readQuotProg U w₀ n_max h_space (base, g_top))
    let v_top := (Memory.spec 0).clientResult s (readValProg U V w₀ n_max h_space (base, g_top))
    let s_wq := (Memory.spec 0).clientState s
      (writeQuotProg U w₀ n_max h_space ((base, g_u), q_top))
    let s_wv := (Memory.spec 0).clientState s_wq
      (writeValProg U V w₀ n_max h_space ((base, g_u), v_top))
    k ≤ slabSize n_max - 1 ∧
    r_top ≤ tailCapPerBucket n_max ∧
    ptr_u_idx < globalMetaLen n_max ∧
    ptr_top_idx < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    t_u ≤ n_max - 1 ∧
    t_top ≤ n_max - 1 ∧
    g_u < n_max ∧
    g_top < n_max ∧
    g_slab < n_max ∧
    TailBijection n_max (gmAt base U V w₀ n_max h_space s_wv.mem)
      (fun b' => gmAt base U V w₀ n_max h_space s_wv.mem (gmRIdx b'))
      (gmAt base U V w₀ n_max h_space s_wv.mem 1) ∧
    1 ≤ gmAt base U V w₀ n_max h_space s_wv.mem (gmRIdx b) ∧
    k + 1 ≤ max n_max 1 := by
  intro u r_top ptr_u_idx ptr_top_idx t_u s1 t_top s2 p_new
    g_u g_top g_slab q_top v_top s_wq s_wv
  obtain ⟨hr_top_cap, hptr_u_lt, hptr_top_lt, h0_lt, htu_le, httop_le, hgu_lt, hgtop_lt,
    hgslab_lt, hr_pos, hk1⟩ := promoteStep_index_bounds h.2 h.1
  have htu_eq : t_u = gmAt base U V w₀ n_max h_space s.mem
      (gmTailPtrIdx n_max b (slabSize n_max - 1 - k)) :=
    clientResult_readGMProg s hptr_u_lt
  have httop_eq : t_top = gmAt base U V w₀ n_max h_space s.mem
      (gmTailPtrIdx n_max b (slabSize n_max + (slabSize n_max - 1 - k))) :=
    clientResult_readGMProg s hptr_top_lt
  have hpnew_eq : p_new = gmAt base U V w₀ n_max h_space s.mem 0 :=
    clientResult_readGMProg s h0_lt
  rw [← htu_eq] at htu_le hgu_lt
  rw [← httop_eq] at httop_le hgtop_lt
  rw [← hpnew_eq] at hgslab_lt
  obtain ⟨_, _, _, _, _, hg1⟩ := writeQuotProg_effect (base := base) (V := V) (h_space := h_space)
    hw hgu_lt ((clientResult_readQuotProg s hgtop_lt).trans_lt (quotAt_lt ..)) s
  obtain ⟨_, _, _, _, _, hg2⟩ := writeValProg_effect (base := base) (h_space := h_space)
    hw hgu_lt ((clientResult_readValProg s hgtop_lt).trans_lt (valAt_lt ..)) s_wq
  have hgm_wv : gmAt base U V w₀ n_max h_space s_wv.mem = gmAt base U V w₀ n_max h_space s.mem := by
    dsimp only [s_wv]; rw [hg2, hg1]
  refine ⟨by have := h.1.2.1; omega, hr_top_cap.le, hptr_u_lt, hptr_top_lt, h0_lt, htu_le, httop_le,
    hgu_lt, hgtop_lt, hgslab_lt, by rw [hgm_wv]; exact h.1.2.2.1, by rw [hgm_wv]; exact hr_pos, hk1⟩

theorem realizes_promoteStepGen :
    Realizes .exact promoteStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      PromoteStepGenPre
      (fun _ _ => 0) := by
  realize
    [realizes_readGMGen, realizes_readQuotGen, realizes_writeQuotGen, realizes_readValGen,
      realizes_writeValGen, realizes_removeLastTailItemGen]
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [promoteStepGenPre_mk, removeLastTailItemGenPre_mk,
      removeLastTailItemGenProg_mk]
    obtain ⟨hdict, hinv, hbp⟩ := h
    obtain ⟨hk, _, hpu, hpt, h0, htu, httop, hgu, hgtop, hgslab, htail', hr1, hk1⟩ :=
      promoteStep_bounds hw ⟨hinv, hbp⟩
    first
    | exact hdict
    | with_reducible assumption
    | exact ⟨hdict, htail', hinv.1, hr1, hbp⟩
    | exact fits_of_le_globalMetaLen hdict hbp hw hnU hU hpu.le
    | exact fits_of_le_globalMetaLen hdict hbp hw hnU hU hpt.le
    | exact fits_of_le_max_n_one hdict hw hnU hU (hgslab.le.trans (le_max_left n_max 1))
    | exact fits_of_le_max_n_one hdict hw hnU hU hk1)

/-! ## Section 2: `PromoteArrInv`, `PromoteLoopInv`, and `promoteSlabProg` -/

/-- Array payload invariant at iteration `k ≤ slabSize n_max` of the slab-promotion loop. -/
structure PromoteArrInv {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α)
    (k : ℕ) (gm : ℕ → ℕ) (arr : ℕ → α) : Prop where
  other_bucket : ∀ b' < numBuckets n_max, b' ≠ b → ∀ j < bCount n_max gm₀ b',
    arr (slotOf n_max gm b' j) = arr₀ (slotOf n_max gm₀ b' j)
  same_slabs : ∀ j < gm₀ (gmQIdx b) * slabSize n_max,
    arr (slotOf n_max gm b j) = arr₀ (slotOf n_max gm₀ b j)
  low_tail : ∀ u < slabSize n_max - k,
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u)) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + u))
  high_tail : ∀ u < slabSize n_max - k,
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u))) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u)))
  shifted_tail : ∀ u, slabSize n_max - k ≤ u → u < slabSize n_max →
    arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u)) =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max + u)))
  new_slab : ∀ k' < k,
    arr (gm₀ 0 * slabSize n_max + k') =
      arr₀ (slotOf n_max gm₀ b (gm₀ (gmQIdx b) * slabSize n_max + (slabSize n_max - 1 - k')))

theorem promoteArrInv_zero {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α) :
    PromoteArrInv n_max b gm₀ arr₀ 0 gm₀ arr₀ := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun u h1 h2 => by omega, fun k' hk' => by omega⟩

private theorem bCount_of_pos {n_max b : ℕ} (hb0 : bucketBits n_max ≠ 0)
    (gm : ℕ → ℕ) (hb : b < numBuckets n_max) :
    bCount n_max gm b = gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b) := by
  unfold bCount; simp only [hb0, ↓reduceIte, hb]

private theorem slotOf_tail_add {n_max b' q r : ℕ} {gm : ℕ → ℕ}
    (hb0 : bucketBits n_max ≠ 0) (hq : gm (gmQIdx b') = q) :
    slotOf n_max gm b' (q * slabSize n_max + r) = n_max - 1 - gm (gmTailPtrIdx n_max b' r) := by
  unfold slotOf
  have hnot : ¬(q * slabSize n_max + r < gm (gmQIdx b') * slabSize n_max) := by rw [hq]; omega
  rw [ite_eq_right hb0, ite_eq_right hnot, hq, Nat.add_sub_cancel_left]

private theorem slotOf_slab_lt_nslabs_mul {n_max b' j : ℕ} {gm : ℕ → ℕ}
    (hb0 : bucketBits n_max ≠ 0) (hb' : b' < numBuckets n_max)
    (hslab : SlabBijection n_max gm (fun c => gm (gmQIdx c)) (gm 0))
    (hj : j < gm (gmQIdx b') * slabSize n_max) :
    slotOf n_max gm b' j < gm 0 * slabSize n_max := by
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  unfold slotOf
  rw [ite_eq_right hb0, ite_eq_left hj]
  have hs_lt : j / slabSize n_max < gm (gmQIdx b') :=
    Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have h1 : (slabPtrOf n_max gm b' (j / slabSize n_max) + 1) * slabSize n_max ≤
      gm 0 * slabSize n_max := Nat.mul_le_mul_right _ (hslab.ptr_lt b' hb' _ hs_lt)
  rw [Nat.add_one_mul] at h1
  have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j hK_pos
  omega

theorem promoteArrInv_step {α : Type*} {n_max b k : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (hk : k < slabSize n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = 2 * slabSize n_max - k)
    (htot : gm 0 * slabSize n_max + k + gm 1 ≤ n_max)
    (harr : PromoteArrInv n_max b gm₀ arr₀ k gm arr) :
    let u := (slabSize n_max - 1) - k
    let r_top := slabSize n_max + u
    let g_u := (n_max - 1) - gm (gmTailPtrIdx n_max b u)
    let g_top := (n_max - 1) - gm (gmTailPtrIdx n_max b r_top)
    let g_del := (n_max - 1) - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
    let g_last := (n_max - 1) - (gm 1 - 1)
    let g_slab := gm 0 * slabSize n_max + k
    let arr₁ := Function.update arr g_u (arr g_top)
    let arr₂ := Function.update arr₁ g_del (arr₁ g_last)
    let arr₃ := Function.update arr₂ g_slab (arr g_u)
    PromoteArrInv n_max b gm₀ arr₀ (k + 1) (gmRemoveTail n_max gm b) arr₃ := by
  intro u r_top g_u g_top g_del g_last g_slab arr₁ arr₂ arr₃
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hTcap : tailCapPerBucket n_max = 2 * slabSize n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0]
  have hr_pos : 1 ≤ gm (gmRIdx b) := by omega
  have htot0 : gm 0 * slabSize n_max + gm 1 ≤ n_max := by omega
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  have htail' := tailBijection_gmRemoveTail hb hr_pos htail
  have hslab' := (slabBijection_gmRemoveTail hb hr_pos htail hslab).2
  have ⟨hupd_slot, hupd_low⟩ := update_slotOf_gmRemoveTail arr₁ hb_pos hb hr_pos htail hslab htot0
  have hu_lt_r : u < gm (gmRIdx b) := by omega
  have hu_cap : u < tailCapPerBucket n_max := by omega
  have htu_lt_gm1 : gm (gmTailPtrIdx n_max b u) < gm 1 := htail.ptr_lt b hb u hu_lt_r
  have hgu_eq_slot : g_u = slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + u) :=
    (slotOf_tail_add hb0 (hq b hb)).symm
  have hgtop_eq_slot : g_top = slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + r_top) :=
    (slotOf_tail_add hb0 (hq b hb)).symm
  have harr1_ne : ∀ x ≠ g_u, arr₁ x = arr x := fun _ h => Function.update_of_ne h _ _
  have harr3_slot : ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmRemoveTail n_max gm b) b',
      arr₃ (slotOf n_max (gmRemoveTail n_max gm b) b' j) = arr₁ (slotOf n_max gm b' j) := by
    intro b' hb' j hj
    have hj' : j < gmRemoveTail n_max gm b (gmQIdx b') * slabSize n_max +
        gmRemoveTail n_max gm b (gmRIdx b') := (bCount_of_pos hb0 _ hb') ▸ hj
    have hne_slab : slotOf n_max (gmRemoveTail n_max gm b) b' j ≠ g_slab := by
      by_cases hj_slab : j < gmRemoveTail n_max gm b (gmQIdx b') * slabSize n_max
      · have hslt := slotOf_slab_lt_nslabs_mul hb0 hb' hslab' hj_slab
        rw [hpres.1] at hslt; omega
      · unfold slotOf
        rw [ite_eq_right hb0, ite_eq_right hj_slab]
        have ht'_lt := htail'.ptr_lt b' hb'
          (j - gmRemoveTail n_max gm b (gmQIdx b') * slabSize n_max) (by omega)
        rw [hpres.2.1] at ht'_lt; omega
    simpa only [arr₃, Function.update_of_ne hne_slab] using hupd_slot b' hb' j hj
  have hslab_ne_gu : ∀ b' < numBuckets n_max, ∀ j < gm₀ (gmQIdx b') * slabSize n_max,
      slotOf n_max gm b' j ≠ g_u := by
    intro b' hb' j hj
    have hslt := slotOf_slab_lt_nslabs_mul hb0 hb' hslab (by rwa [hq b' hb'])
    omega
  have htail_ne_gu : ∀ b' < numBuckets n_max, ∀ r' < gm (gmRIdx b'), (b' ≠ b ∨ r' ≠ u) →
      slotOf n_max gm b' (gm₀ (gmQIdx b') * slabSize n_max + r') ≠ g_u := by
    intro b' hb' r' hr' hne heq
    rw [slotOf_tail_add hb0 (hq b' hb')] at heq
    have ht'_lt := htail.ptr_lt b' hb' r' hr'
    have ht_eq : gm (gmTailPtrIdx n_max b' r') = gm (gmTailPtrIdx n_max b u) := by
      dsimp only [g_u] at heq; omega
    have hown := congrArg (fun p => gm (gmTailOwnerIdx n_max p)) ht_eq
    rw [htail.owner_ptr b' hb' r' hr', htail.owner_ptr b hb u hu_lt_r] at hown
    obtain ⟨hb_eq, hr_eq⟩ :=
      flat_descriptor_inj (lt_of_lt_of_le hr' (htail.r_le b' hb')) hu_cap hown
    exact hne.elim (· hb_eq) (· hr_eq)
  have hbc_other : ∀ b' < numBuckets n_max, b' ≠ b →
      bCount n_max (gmRemoveTail n_max gm b) b' = bCount n_max gm₀ b' := by
    intro b' hb' hne
    rw [bCount_of_pos hb0 _ hb', bCount_of_pos hb0 _ hb',
      hpres.2.2.2.2.1 b' hb', hq b' hb', hpres.2.2.2.1 b' hb' hne, hr_other b' hb' hne]
  have hbc_b : bCount n_max (gmRemoveTail n_max gm b) b =
      gm₀ (gmQIdx b) * slabSize n_max + (2 * slabSize n_max - (k + 1)) := by
    rw [bCount_of_pos hb0 _ hb, hpres.2.2.2.2.1 b hb, hq b hb, hpres.2.2.1, hr_b]; omega
  have harr_tail : ∀ t' < 2 * slabSize n_max - (k + 1), t' ≠ u →
      arr₃ (slotOf n_max (gmRemoveTail n_max gm b) b (gm₀ (gmQIdx b) * slabSize n_max + t')) =
        arr (slotOf n_max gm b (gm₀ (gmQIdx b) * slabSize n_max + t')) := fun t' ht' hne => by
    rw [harr3_slot b hb _ (by rw [hbc_b]; omega),
      harr1_ne _ (htail_ne_gu b hb t' (by omega) (Or.inr hne))]
  refine ⟨?_, ?_, fun u' hu' => ?_, fun u' hu' => ?_, fun u' hu'_ge hu'_lt => ?_, fun k' hk' => ?_⟩
  · intro b' hb' hne j hj
    rw [harr3_slot b' hb' j (by rwa [hbc_other b' hb' hne])]
    by_cases hj_slab : j < gm₀ (gmQIdx b') * slabSize n_max
    · rw [harr1_ne _ (hslab_ne_gu b' hb' j hj_slab)]
      exact harr.other_bucket b' hb' hne j hj
    · set r' := j - gm₀ (gmQIdx b') * slabSize n_max
      have hj_eq : j = gm₀ (gmQIdx b') * slabSize n_max + r' := by omega
      have hr'_lt : r' < gm (gmRIdx b') := by
        rw [bCount_of_pos hb0 _ hb'] at hj; rw [hr_other b' hb' hne]; omega
      rw [hj_eq, harr1_ne _ (htail_ne_gu b' hb' r' hr'_lt (Or.inl hne)), ← hj_eq]
      exact harr.other_bucket b' hb' hne j hj
  · intro j hj
    rw [harr3_slot b hb j (by rw [hbc_b]; omega), harr1_ne _ (hslab_ne_gu b hb j hj)]
    exact harr.same_slabs j hj
  · exact (harr_tail u' (by omega) (by omega)).trans (harr.low_tail u' (by omega))
  · exact (harr_tail (slabSize n_max + u') (by omega) (by omega)).trans
      (harr.high_tail u' (by omega))
  · by_cases heq : u' = u
    · subst heq
      rw [harr3_slot b hb _ (by rw [hbc_b]; omega), ← hgu_eq_slot]
      simpa only [arr₁, Function.update_self, hgtop_eq_slot] using harr.high_tail u (by omega)
    · exact (harr_tail u' (by omega) heq).trans (harr.shifted_tail u' (by omega) hu'_lt)
  · dsimp only [arr₃]
    have h0_mul : gm 0 * slabSize n_max = gm₀ 0 * slabSize n_max := by rw [h0]
    by_cases heq : k' = k
    · subst heq
      rw [← h0_mul, Function.update_self, hgu_eq_slot]
      exact harr.low_tail u (by omega)
    · dsimp only [arr₂, g_del, g_last, g_u, g_slab]
      have hlow :=
        (hupd_low (gm₀ 0 * slabSize n_max + k') (by omega)).trans (harr1_ne _ (by omega))
      rw [Function.update_of_ne (by omega), hlow]
      exact harr.new_slab k' (by omega)

/-- Loop invariant at step `k ≤ slabSize n_max` of `promoteLoopProg`. -/
structure PromoteLoopInv (U V w₀ n_max h_space base b : ℕ) (s₀ : Memory.State)
    (k : ℕ) (s : Memory.State) : Prop where
  b_lt : b < numBuckets n_max
  k_le : k ≤ slabSize n_max
  frontier_eq : s.frontier = s₀.frontier
  mem_out : ∀ a, ¬(base + offQuot h_space ≤ a ∧
    a < base + totalSpace U V w₀ n_max h_space) → s.mem a = s₀.mem a
  lm_eq : lmAt base U V w₀ n_max h_space s.mem = lmAt base U V w₀ n_max h_space s₀.mem
  tail_bij : TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1)
  slab_bij : SlabBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmQIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 0)
  gm0_eq : gmAt base U V w₀ n_max h_space s.mem 0 = gmAt base U V w₀ n_max h_space s₀.mem 0
  gm1_eq : gmAt base U V w₀ n_max h_space s.mem 1 + k = gmAt base U V w₀ n_max h_space s₀.mem 1
  rb_eq : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) = 2 * slabSize n_max - k
  r_other : ∀ b' < numBuckets n_max, b' ≠ b →
    gmAt base U V w₀ n_max h_space s.mem (gmRIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b')
  q_eq : ∀ b' < numBuckets n_max,
    gmAt base U V w₀ n_max h_space s.mem (gmQIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmQIdx b')
  tot_le : gmAt base U V w₀ n_max h_space s.mem 0 * slabSize n_max + k +
    gmAt base U V w₀ n_max h_space s.mem 1 ≤ n_max
  quot_inv : PromoteArrInv n_max b (gmAt base U V w₀ n_max h_space s₀.mem)
    (quotAt base U w₀ n_max h_space s₀.mem) k
    (gmAt base U V w₀ n_max h_space s.mem) (quotAt base U w₀ n_max h_space s.mem)
  val_inv : PromoteArrInv n_max b (gmAt base U V w₀ n_max h_space s₀.mem)
    (valAt base U V w₀ n_max h_space s₀.mem) k
    (gmAt base U V w₀ n_max h_space s.mem) (valAt base U V w₀ n_max h_space s.mem)

theorem promoteStepInv_of_loopInv {U V w₀ n_max h_space base b k : ℕ} {s₀ s : Memory.State}
    (hinv : PromoteLoopInv U V w₀ n_max h_space base b s₀ k s) (hk : k < slabSize n_max) :
    PromoteStepInv U V w₀ n_max h_space base b k s :=
  ⟨hinv.b_lt, hk, hinv.tail_bij, hinv.slab_bij, hinv.rb_eq, hinv.tot_le⟩

theorem promoteLoopInv_step {U V w₀ n_max h_space base b k : ℕ} {s₀ s : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (hinv : PromoteLoopInv U V w₀ n_max h_space base b s₀ k s) (hk : k < slabSize n_max) :
    let s' := (Memory.spec 0).clientState s
      (promoteStepProg U V w₀ n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (promoteStepProg U V w₀ n_max h_space ((base, b), k)) = k + 1 ∧
    PromoteLoopInv U V w₀ n_max h_space base b s₀ (k + 1) s' := by
  have hstep := promoteStepInv_of_loopInv hinv hk
  obtain ⟨hres, hf, hout, hq, hv, hl, hgm⟩ :=
    promoteStepProg_effect hw hb_pos s hstep
  have hr_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) := hinv.rb_eq ▸ by omega
  have hpres := gmRemoveTail_preserves_nonTail hinv.b_lt hr_pos hinv.tail_bij
  have htail' := tailBijection_gmRemoveTail hinv.b_lt hr_pos hinv.tail_bij
  have ⟨_, hslab'⟩ := slabBijection_gmRemoveTail hinv.b_lt hr_pos hinv.tail_bij hinv.slab_bij
  have := r_le_ntails_of_tailBijection hinv.tail_bij hinv.b_lt
  have harr_step {arr₀ arr : ℕ → ℕ} :=
    promoteArrInv_step (arr₀ := arr₀) (arr := arr) hb_pos hinv.b_lt hk hinv.tail_bij hinv.slab_bij
      hinv.gm0_eq hinv.q_eq hinv.r_other hinv.rb_eq hinv.tot_le
  exact ⟨hres, ⟨hinv.b_lt, by omega, hf.trans hinv.frontier_eq,
    fun a ha => (hout a ha).trans (hinv.mem_out a ha), hl.trans hinv.lm_eq,
    hgm ▸ htail', hgm ▸ hslab',
    by rw [hgm, hpres.1, hinv.gm0_eq],
    by rw [hgm, hpres.2.1]; have := hinv.gm1_eq; omega,
    by rw [hgm, hpres.2.2.1, hinv.rb_eq]; omega,
    fun b' hb' hne => by rw [hgm, hpres.2.2.2.1 b' hb' hne, hinv.r_other b' hb' hne],
    fun b' hb' => by rw [hgm, hpres.2.2.2.2.1 b' hb', hinv.q_eq b' hb'],
    by rw [hgm, hpres.1, hpres.2.1]; have := hinv.tot_le; omega,
    hgm ▸ hq ▸ harr_step hinv.quot_inv,
    hgm ▸ hv ▸ harr_step hinv.val_inv⟩⟩

theorem iterate_promoteStepProg_spec {U V w₀ n_max h_space w base b : ℕ} {s₀ : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max) :
    ∀ m k (s : Memory.State),
      k + m ≤ slabSize n_max →
      PromoteLoopInv U V w₀ n_max h_space base b s₀ k s →
      PromoteLoopInv U V w₀ n_max h_space base b s₀ (k + m)
        ((Memory.spec 0).clientState s
          (iterate (promoteStepProg U V w₀ n_max h_space) (base, b) m k)) ∧
      memoryCost (iterate (promoteStepProg U V w₀ n_max h_space) (base, b) m k) s = 66 * m ∧
      (DictEnvGen w (mkDictParams U V w₀ n_max h_space) base →
        iterationSafe (promoteStepProg U V w₀ n_max h_space)
          (fun w x s => PromoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
          w (base, b) m k s) := by
  intro m
  induction m with
  | zero => exact fun _ _ _ hinv => ⟨hinv, rfl, fun _ => trivial⟩
  | succ m ih =>
    intro k s hkm hinv
    have hk_lt : k < slabSize n_max := by omega
    obtain ⟨hres, hinv'⟩ := promoteLoopInv_step hw hb_pos hinv hk_lt
    obtain ⟨hfinal, hcost, hsafe⟩ := ih (k + 1)
      ((Memory.spec 0).clientState s (promoteStepProg U V w₀ n_max h_space ((base, b), k)))
      (by omega) hinv'
    refine ⟨?_, ?_, fun hdenv => ?_⟩
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hres, Nat.add_succ, ← Nat.succ_add]
      exact hfinal
    · simp only [iterate, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_promoteStepProg, hres, hcost]
      omega
    · simp only [iterationSafe, hres]
      exact ⟨⟨hdenv, promoteStepInv_of_loopInv hinv hk_lt, hb_pos⟩, hsafe hdenv⟩

/-- Parameter-free wrapper for `iterate promoteStepGenProg` with signature
`(((dp, (base, b)), k), m) → Memory.Prog ℕ` matching `Realizes.iterate₀`. -/
def promoteLoopGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate promoteStepGenProg d.1.1 d.2 d.1.2

/-- Wrapper for `iterate (promoteStepProg U V w n_max h_space)` with signature
`(((base, b), k), m) → Memory.Prog ℕ` matching `Realizes.iterate₀`. -/
def promoteLoopProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate (promoteStepProg U V w n_max h_space) d.1.1 d.2 d.1.2

@[simp] theorem iterate_promoteStepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) :
    iterate promoteStepGenProg (mkDictParams U V w n_max h_space, d) m k =
      iterate (promoteStepProg U V w n_max h_space) d m k :=
  iterate_congr (fun a => promoteStepGenProg_mk U V w n_max h_space d a) m k

@[simp] theorem promoteLoopGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    promoteLoopGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      promoteLoopProg U V w n_max h_space ((d1, d2), d3) :=
  iterate_promoteStepGenProg_mk U V w n_max h_space d1 d3 d2

@[simp] theorem iterationSafe_promoteStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) (s : Memory.State) :
    iterationSafe promoteStepGenProg PromoteStepGenPre w
        (mkDictParams U V w₀ n_max h_space, d) m k s ↔
      iterationSafe (promoteStepProg U V w₀ n_max h_space)
        (fun w x s => PromoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w d m k s :=
  iterationSafe_congr (fun a => promoteStepGenProg_mk U V w₀ n_max h_space d a)
    (fun a t => promoteStepGenPre_mk U V w₀ n_max h_space w d a t) m k s

theorem realizes_promoteLoopGen :
    Realizes .exact promoteLoopGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s =>
        iterationSafe promoteStepGenProg PromoteStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_promoteStepGen
    one_le_memoryCost_promoteStepGenProg

/-- Parameter-free `Memory.Prog` operation promoting `K = slabSize n_max` tail items of bucket
`b = d.2.2` at `base = d.2.1` into a new full slab. -/
@[expose]
def promoteSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let _ ← promoteLoopGenProg ((d, 0), dpSlabSize d.1)
  gmPushSlabGenProg d

/-- `Memory.Prog` operation promoting `K = slabSize n_max` tail items of bucket `b = d.2` at
`base = d.1` (`gm (gmRIdx b) = 2 * K`) into a new full slab via `promoteLoopProg` followed by
`gmPushSlabProg`. -/
@[expose]
def promoteSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit :=
  promoteSlabGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem promoteSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    promoteSlabGenProg (mkDictParams U V w n_max h_space, d) =
      promoteSlabProg U V w n_max h_space d := by
  rfl

/-- Pure entry invariant for `promoteSlabProg`. -/
@[expose]
def PromoteSlabInv (U V w₀ n_max h_space base b : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 2 * slabSize n_max ∧
  (∀ b' < numBuckets n_max, b' ≠ b →
    gm (gmRIdx b') < tailCapPerBucket n_max ∧
    (0 < gm (gmQIdx b') → 1 ≤ gm (gmRIdx b'))) ∧
  gm 0 * slabSize n_max + gm 1 ≤ n_max

/-- Precondition for `promoteSlabProg` in `Realizes`. -/
@[expose]
def PromoteSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  PromoteSlabInv U V w₀ n_max h_space base b s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `promoteSlabGenProg`. -/
@[expose]
def PromoteSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  PromoteSlabInv (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) d.2.1 d.2.2 s ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem promoteSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    PromoteSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      PromoteSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem promoteLoopInv_zero {U V w₀ n_max h_space base b : ℕ} {s₀ : Memory.State}
    (hpre : PromoteSlabInv U V w₀ n_max h_space base b s₀) :
    PromoteLoopInv U V w₀ n_max h_space base b s₀ 0 s₀ := by
  rcases hpre with ⟨hb, htail, hslab, hrb, _, htot⟩
  refine ⟨hb, Nat.zero_le _, rfl, fun _ _ => rfl, rfl, htail, hslab, rfl,
    Nat.add_zero _, by omega, fun _ _ _ => rfl, fun _ _ => rfl, by omega,
    promoteArrInv_zero _ _ _ _, promoteArrInv_zero _ _ _ _⟩

theorem slotOf_gmPushSlab_preserve {α : Type*} {n_max b : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = slabSize n_max)
    (_hr0_b : gm₀ (gmRIdx b) = 2 * slabSize n_max)
    (htot : (gm 0 + 1) * slabSize n_max + gm 1 ≤ n_max)
    (harr : PromoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm arr) :
    ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmPushSlab n_max gm b) b',
      arr (slotOf n_max (gmPushSlab n_max gm b) b' j) = arr₀ (slotOf n_max gm₀ b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have htot' : (gm 0 + 1) * slabSize n_max ≤ n_max := by omega
  have hp_lt : gm 0 < maxFullSlabs n_max := nslabs_lt_maxFullSlabs_of_mul_le hb_pos htot'
  have hf := gmPushSlab_fields gm hb
  have ⟨hptr, _⟩ := slabBijection_gmPushSlab hb hp_lt hslab
  have htail_ptr : ∀ b' < numBuckets n_max, ∀ r < tailCapPerBucket n_max,
      gmPushSlab n_max gm b (gmTailPtrIdx n_max b' r) = gm (gmTailPtrIdx n_max b' r) := by
    intro b' hb' r hr
    have hd_lt := mul_tailCapPerBucket_add_lt_maxTailItems hb' hr
    exact hf.2.2.2.1 _ (by wram_omega) (by wram_omega)
  intro b' hb' j hj
  rw [bCount_of_pos hb0 _ hb'] at hj
  by_cases hbeq : b' = b
  · subst b'
    have hq_b_push : gmPushSlab n_max gm b (gmQIdx b) = gm (gmQIdx b) + 1 := by
      rw [hf.2.2.2.2.1 b hb, ite_eq_left rfl]
    rw [hq_b_push, hf.2.2.1 b hb, hq b hb, hr_b] at hj
    conv_lhs => unfold slotOf
    rw [ite_eq_right hb0, hq_b_push, hq b hb]
    split_ifs with hj_slab
    · have hs_lt : j / slabSize n_max < gmPushSlab n_max gm b (gmQIdx b) := by
        rw [hq_b_push, hq b hb]
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      by_cases hj_old : j < gm₀ (gmQIdx b) * slabSize n_max
      · have hs_ne : j / slabSize n_max ≠ gm (gmQIdx b) :=
          (hq b hb ▸ Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ hj_old)).ne
        rw [hptr b hb (j / slabSize n_max) hs_lt, ite_eq_right (fun h => hs_ne h.2),
          ← harr.same_slabs j hj_old]
        simp only [slotOf, hb0, hq b hb, hj_old, ↓reduceIte]
      · set u := j - gm₀ (gmQIdx b) * slabSize n_max
        have hu_lt : u < slabSize n_max := by rw [Nat.add_one_mul] at hj_slab; omega
        have hj_eq : j = gm₀ (gmQIdx b) * slabSize n_max + u := by omega
        have hs_eq : j / slabSize n_max = gm (gmQIdx b) := by
          rw [hq b hb, hj_eq, Nat.mul_comm, Nat.mul_add_div hK_pos,
            Nat.div_eq_of_lt hu_lt, Nat.add_zero]
        have hmod_eq : j % slabSize n_max = u := by
          rw [hj_eq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hu_lt]
        rw [hptr b hb (j / slabSize n_max) hs_lt, ite_eq_left ⟨rfl, hs_eq⟩, hmod_eq, h0]
        have hsub : slabSize n_max - 1 - (slabSize n_max - 1 - u) = u := by omega
        simpa only [hsub, ← hj_eq] using harr.new_slab (slabSize n_max - 1 - u) (by omega)
    · set u := j - (gm₀ (gmQIdx b) + 1) * slabSize n_max
      have hu_lt : u < slabSize n_max := by omega
      have hu_cap : u < tailCapPerBucket n_max := by
        unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
      rw [htail_ptr b hb u hu_cap, ← slotOf_tail_add hb0 (hq b hb),
        harr.shifted_tail u (by omega) hu_lt]
      congr 2; dsimp only [u]; rw [Nat.add_one_mul] at hj_slab ⊢; omega
  · have hq_b'_push : gmPushSlab n_max gm b (gmQIdx b') = gm (gmQIdx b') := by
      rw [hf.2.2.2.2.1 b' hb', ite_eq_right hbeq]
    rw [hq_b'_push, hf.2.2.1 b' hb', hq b' hb', hr_other b' hb' hbeq] at hj
    have hslot_eq : slotOf n_max (gmPushSlab n_max gm b) b' j = slotOf n_max gm b' j := by
      unfold slotOf
      rw [ite_eq_right hb0, ite_eq_right hb0, hq_b'_push, hq b' hb']
      split_ifs with hj_slab
      · rw [hptr b' hb' (j / slabSize n_max)
            (hq_b'_push.symm ▸ hq b' hb' ▸ Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ hj_slab)),
          ite_eq_right (fun h => hbeq h.1)]
      · have hr'_lt : j - gm₀ (gmQIdx b') * slabSize n_max < gm (gmRIdx b') := by
          rw [hr_other b' hb' hbeq]; omega
        rw [htail_ptr b' hb' _ (lt_of_lt_of_le hr'_lt (htail.r_le b' hb'))]
    rw [hslot_eq]
    exact harr.other_bucket b' hb' hbeq j (by rw [bCount_of_pos hb0 _ hb']; exact hj)

/-- Under `PromoteSlabInv U V w n_max h_space base b s` (`gm (gmRIdx b) = 2 * slabSize n_max`),
`promoteSlabProg` runs in `memoryCost ≤ 66 * slabSize n_max + 38` and preserves `frontier`, `lmAt`,
and memory outside `[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It restores
`SlotStoreInv n_max gm'` with `gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1`,
`gm' (gmRIdx b) = slabSize n_max`, and unchanged `(gmQIdx b', gmRIdx b')` for `b' ≠ b`. It also
preserves `bCount` and every logical `(quotAt, valAt)` entry at `slotOf` across all buckets. -/
theorem promoteSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : PromoteSlabInv U V w n_max h_space base b s) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1 ∧
    gm' (gmRIdx b) = slabSize n_max ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (promoteSlabProg U V w n_max h_space (base, b)) s ≤
      66 * slabSize n_max + 38 := by
  intro gm₀ s' gm'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  obtain ⟨hloopK, hcost_loop, _⟩ :=
    iterate_promoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  set s₁ := (Memory.spec 0).clientState s
    (promoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change PromoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  let gm₁ := gmAt base U V w n_max h_space s₁.mem
  have htot_push : (gm₁ 0 + 1) * slabSize n_max + gm₁ 1 ≤ n_max := by
    rw [Nat.add_one_mul]; have := hloopK.tot_le; omega
  have hp_lt1 : gm₁ 0 < maxFullSlabs n_max :=
    nslabs_lt_maxFullSlabs_of_mul_le hb_pos (by omega)
  obtain ⟨hf_push, hout_push, hq_push, hv_push, hl_push, hgm_push⟩ :=
    gmPushSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hp_lt1
  have hst : s' =
      (Memory.spec 0).clientState s₁ (gmPushSlabProg U V w n_max h_space (base, b)) := by
    simp only [s', promoteSlabProg, promoteSlabGenProg, p_slabSize_mk, promoteLoopGenProg_mk,
      gmPushSlabGenProg_mk]
    rw [StateTransitionSpec.clientState_bind]
  have hgm'_eq : gm' = gmPushSlab n_max gm₁ b := by dsimp only [gm']; rw [hst, hgm_push]
  have hf_fields := gmPushSlab_fields gm₁ hloopK.b_lt
  have ⟨_, hslab2⟩ := slabBijection_gmPushSlab hloopK.b_lt hp_lt1 hloopK.slab_bij
  have htail2 := tailBijection_gmPushSlab hloopK.b_lt hloopK.tail_bij
  have hqb : gm' (gmQIdx b) = gm₀ (gmQIdx b) + 1 := by
    rw [hgm'_eq, hf_fields.2.2.2.2.1 b hloopK.b_lt, ite_eq_left rfl]
    exact congrArg (· + 1) (hloopK.q_eq b hloopK.b_lt)
  have hrb1 : gm₁ (gmRIdx b) = slabSize n_max := by
    dsimp only [gm₁]; rw [hloopK.rb_eq]; omega
  have hrb : gm' (gmRIdx b) = slabSize n_max := by
    rw [hgm'_eq, hf_fields.2.2.1 b hloopK.b_lt, hrb1]
  have hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
    intro b' hb' hne
    rw [hgm'_eq, hf_fields.2.2.2.2.1 b' hb', ite_eq_right hne, hf_fields.2.2.1 b' hb']
    exact ⟨hloopK.q_eq b' hb', hloopK.r_other b' hb' hne⟩
  have hinv2 : SlotStoreInv n_max gm' := by
    refine ⟨fun _ => by omega, fun _ => hgm'_eq ▸ htail2,
      fun _ => hgm'_eq ▸ hslab2, fun _ b' hb' => ?_, ?_⟩
    · by_cases hbeq : b' = b
      · subst b'; rw [hrb]; unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
      · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
        exact hpre.2.2.2.2.1 b' hb' hbeq
    · simpa only [hgm'_eq, hf_fields.1, hf_fields.2.1] using fun _ => htot_push
  have hbc : ∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b' := by
    intro b' hb'
    rw [bCount_of_pos hb0 _ hb', bCount_of_pos hb0 _ hb']
    by_cases hbeq : b' = b
    · subst b'; rw [hqb, hrb]; dsimp only [gm₀]; rw [hpre.2.2.2.1, Nat.add_one_mul]; omega
    · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
  have hpres_arr : ∀ {arr₀ arr : ℕ → ℕ},
      PromoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm₁ arr →
      ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
        arr (slotOf n_max gm' b' j) = arr₀ (slotOf n_max gm₀ b' j) := fun harr b' hb' j hj => by
    rw [hgm'_eq] at hj ⊢
    exact slotOf_gmPushSlab_preserve hb_pos hloopK.b_lt hloopK.tail_bij hloopK.slab_bij
      hloopK.gm0_eq hloopK.q_eq hloopK.r_other hrb1 hpre.2.2.2.1 htot_push harr b' hb' j hj
  refine ⟨by rw [hst, hf_push, hloopK.frontier_eq],
    fun a ha => by
      have ha' : ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) := by wram_omega [ha]
      rw [hst, hout_push a ha', hloopK.mem_out a ha],
    by rw [hst, hl_push, hloopK.lm_eq],
    hinv2, hqb, hrb, hother, hbc,
    fun b' hb' j hj => by
      rw [hst, hq_push, hv_push]
      exact ⟨hpres_arr hloopK.quot_inv b' hb' j hj, hpres_arr hloopK.val_inv b' hb' j hj⟩, ?_⟩
  have hpush_cost := memoryCost_gmPushSlabProg_le U V w n_max h_space (base, b) s₁
  simp only [s₁, promoteSlabProg, promoteSlabGenProg, p_slabSize_mk, promoteLoopGenProg_mk,
    gmPushSlabGenProg_mk, promoteLoopProg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    hcost_loop] at hpush_cost ⊢
  omega

theorem realizes_promoteSlabGen :
    Realizes .exact promoteSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      PromoteSlabGenPre
      (fun _ _ => 0) := by
  realizeDictWith [promoteSlabGenPre_mk, iterationSafe_promoteStepGenProg_mk,
    promoteLoopGenProg_mk, gmPushSlabGenPre_mk, gmPushSlabGenProg_mk]
    using [realizes_promoteLoopGen, realizes_gmPushSlabGen]
  · exact (iterate_promoteStepProg_spec hw h.2.2 (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero h.2.1)).2.2 h.1
  · rcases d with ⟨base, b⟩
    have hloopK := (iterate_promoteStepProg_spec (w := w) hw h.2.2 (slabSize n_max) 0 s
      (by omega) (promoteLoopInv_zero h.2.1)).1
    have htot := hloopK.tot_le
    refine ⟨h.1, hloopK.slab_bij, h.2.1.1, nslabs_lt_maxFullSlabs_of_mul_le h.2.2 ?_, h.2.2⟩
    dsimp only [GmPushSlabPre, promoteLoopProg] at htot ⊢
    rw [Nat.add_one_mul]
    omega

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
