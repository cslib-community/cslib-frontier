/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.WramOmega

/-!
# `Memory.Prog` Slab Demotion Loop (`demoteStepProg`, `demoteLoopProg`, `demoteSlabProg`)

This module implements the `K = slabSize n_max`-step slab-demotion loop for the fixed-capacity
succinct dictionary using `Memory.Prog`, `iterate`, and the `realize` tactic (`Realizes.iterate₀`).
When a bucket `b` has `gm (gmRIdx b) = 0` tail items and `1 ≤ gm (gmQIdx b)` full slabs after
removing its last tail item, `demoteSlabProg` moves the `K` items from the top slab
`p_del = gm (gmSlabTopIdx b)` into the tail of bucket `b`, compacts the physical slab pool by
copying the `K` items of `p_last = gm 0 - 1` into `p_del`, and pops the top slab descriptor via
`gmPopSlabProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteStepProg`: single step `k < slabSize n_max`
  of slab demotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteLoopProg`: `K`-step iteration of
  `demoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteSlabProg`: complete slab demotion
  (`demoteLoopProg` followed by `gmPopSlabProg`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DemoteSlabInv`: entry invariant for
  `demoteSlabProg` (`gm (gmRIdx b) = 0 ∧ 0 < gm (gmQIdx b)`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteStepProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_demoteStepGen`: single-step invariant
  preservation and `Realizes` certificate for `demoteStepProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.demoteSlabProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_demoteSlabGen`: full-slab demotion
  invariant preservation, `O(K)` `memoryCost`, and `Realizes` certificate for `demoteSlabProg`.
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

/-! ## Section 1: Single step `demoteStepProg` -/

/-- Parameter-free single step `k < slabSize n_max` of slab demotion for
`x = ((dp, (base, b)), k)`. -/
@[expose]
def demoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let dp := x.1.1
  let base := x.1.2.1
  let b := x.1.2.2
  let k := x.2
  let u := dpSlabSizeSubOne dp - k
  let p_del ← readGMGenProg (dp, (base, 4 + 3 * b + 2))
  let n_slabs ← readGMGenProg (dp, (base, 0))
  let p_last := n_slabs - 1
  let g_del := p_del * dpSlabSize dp + u
  let g_last := p_last * dpSlabSize dp + u
  let q_del ← readQuotGenProg (dp, (base, g_del))
  let v_del ← readValGenProg (dp, (base, g_del))
  let q_last ← readQuotGenProg (dp, (base, g_last))
  let v_last ← readValGenProg (dp, (base, g_last))
  let t_new ← appendTailItemGenProg (dp, (base, b))
  let g_tail := dpNMaxSubOne dp - t_new
  writeQuotGenProg (dp, ((base, g_del), q_last))
  writeValGenProg (dp, ((base, g_del), v_last))
  writeQuotGenProg (dp, ((base, g_tail), q_del))
  let _ ← writeValGenProg (dp, ((base, g_tail), v_del))
  pure (k + 1)

/-- One iteration (`0 ≤ k < slabSize n_max`) of the slab-demotion loop for bucket `b = x.1.2`
at `base = x.1.1` with loop index `k = x.2`.
For `u = (slabSize n_max - 1) - k`, `p_del = gm (gmSlabTopIdx b)`, and `p_last = gm 0 - 1`:
1. Reads `(q_del, v_del)` at `g_del = p_del * slabSize n_max + u` and `(q_last, v_last)` at
   `g_last = p_last * slabSize n_max + u`.
2. Appends a new tail item `t_new = gm 1` to bucket `b` (`g_tail = (n_max - 1) - t_new`).
3. Writes `(q_last, v_last)` to `g_del` first, and `(q_del, v_del)` to `g_tail` second,
   then returns `k + 1`. -/
@[expose]
def demoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  demoteStepGenProg ((mkDictParams U V w n_max h_space, x.1), x.2)

@[simp] theorem demoteStepGenProg_mk (U V w n_max h_space : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ) :
    demoteStepGenProg ((mkDictParams U V w n_max h_space, d1), d2) =
      demoteStepProg U V w n_max h_space (d1, d2) := by
  rfl

@[simp]
theorem memoryCost_demoteStepProg (U V w n_max h_space : ℕ) (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (demoteStepProg U V w n_max h_space x) s = 48 := by
  simp [demoteStepProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    demoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk, p_nMaxSubOne_mk, readGMGenProg_mk,
    readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk,
    appendTailItemGenProg_mk]

theorem one_le_memoryCost_demoteStepGenProg (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (demoteStepGenProg x) s := by
  unfold demoteStepGenProg readGMGenProg readPackedGenProg
  dsimp only
  rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedProg]
  omega

/-- Pure state invariant for step `k` (`k < slabSize n_max`) of `demoteStepProg`. -/
@[expose]
def DemoteStepInv (U V w₀ n_max h_space base b k : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  k < slabSize n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = k ∧
  1 ≤ gm (gmQIdx b) ∧
  (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max

/-- Precondition for `demoteStepProg` in `Realizes`. -/
@[expose]
def DemoteStepPre (U V w₀ n_max h_space w base b k : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  DemoteStepInv U V w₀ n_max h_space base b k s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `demoteStepGenProg`. -/
@[expose]
def DemoteStepGenPre (w : ℕ) (x : (DictParams × (ℕ × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w x.1.1 x.1.2.1 ∧
  DemoteStepInv (dpU x.1.1) (dpV x.1.1) (dpW x.1.1) (dpNMax x.1.1) (dpHSpace x.1.1)
    x.1.2.1 x.1.2.2 x.2 s ∧
  0 < bucketBits (dpNMax x.1.1)

@[simp] theorem demoteStepGenPre_mk (U V w₀ n_max h_space w : ℕ) (d1 : ℕ × ℕ) (d2 : ℕ)
    (s : Memory.State) :
    DemoteStepGenPre w ((mkDictParams U V w₀ n_max h_space, d1), d2) s ↔
      DemoteStepPre U V w₀ n_max h_space w d1.1 d1.2 d2 s := Iff.rfl

/-- Bounds for the reads and writes of `demoteStepProg`, stated on the results of its reads,
together with the precondition (apart from `DictEnvGen`) of its `appendTailItemProg` call; shared
by `realizes_demoteStepGen` and `validProg_demoteStep`. -/
private theorem demoteStep_bounds {U V w₀ n_max h_space base b k : ℕ}
    {s : Memory.State}
    (hw : 0 < w₀)
    (h : DemoteStepInv U V w₀ n_max h_space base b k s ∧ 0 < bucketBits n_max) :
    let u := (slabSize n_max - 1) - k
    let e_pdel := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (base, 4 + 3 * b + 2))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (base, 4 + 3 * b + 2))
    let e_nslabs := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (base, 0))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (base, 0))
    let e_plast := e_nslabs - 1
    let g_del := e_pdel * slabSize n_max + u
    let g_last := e_plast * slabSize n_max + u
    let s3 := (Memory.spec 0).clientState s2
      (readQuotProg U w₀ n_max h_space (base, g_del))
    let s4 := (Memory.spec 0).clientState s3
      (readValProg U V w₀ n_max h_space (base, g_del))
    let s5 := (Memory.spec 0).clientState s4
      (readQuotProg U w₀ n_max h_space (base, g_last))
    let s6 := (Memory.spec 0).clientState s5
      (readValProg U V w₀ n_max h_space (base, g_last))
    let e_tnew := (Memory.spec 0).clientResult s6
      (appendTailItemProg U V w₀ n_max h_space (base, b))
    let g_tail := (n_max - 1) - e_tnew
    k ≤ slabSize n_max - 1 ∧
    4 + 3 * b + 2 < globalMetaLen n_max ∧
    0 < globalMetaLen n_max ∧
    1 ≤ e_nslabs ∧
    g_del < n_max ∧
    g_last < n_max ∧
    (TailBijection n_max (gmAt base U V w₀ n_max h_space s6.mem)
        (fun b' => gmAt base U V w₀ n_max h_space s6.mem (gmRIdx b'))
        (gmAt base U V w₀ n_max h_space s6.mem 1) ∧
      b < numBuckets n_max ∧
      gmAt base U V w₀ n_max h_space s6.mem (gmRIdx b) < tailCapPerBucket n_max ∧
      0 < bucketBits n_max) ∧
    e_tnew ≤ n_max - 1 ∧
    g_tail < n_max ∧
    k + 1 ≤ max n_max 1 := by
  rcases h with ⟨⟨hb, hk, htail, hslab, hrb, hqb_pos, htot⟩, hb_pos⟩
  intro u e_pdel s1 e_nslabs s2 e_plast g_del g_last s3 s4 s5 s6 e_tnew g_tail
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hK_le : slabSize n_max ≤ max n_max 1 := slabSize_le_max_n_one n_max
  have hp_del_lt := hslab.top_lt hb (by omega)
  have hgm0_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem 0 := by omega
  have htop_idx_lt : 4 + 3 * b + 2 < globalMetaLen n_max := gmSlabTopIdx_lt hb_pos hb
  have h0_idx_lt : 0 < globalMetaLen n_max := by wram_omega
  have hr_cap : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hrb]; omega
  have hepdel : e_pdel = gmAt base U V w₀ n_max h_space s.mem (gmSlabTopIdx b) :=
    clientResult_readGMProg s htop_idx_lt
  have henslabs : e_nslabs = gmAt base U V w₀ n_max h_space s.mem 0 :=
    clientResult_readGMProg s h0_idx_lt
  have hmul : e_pdel * slabSize n_max ≤ e_plast * slabSize n_max :=
    Nat.mul_le_mul_right _ (by dsimp only [e_plast]; rw [hepdel, henslabs]; omega)
  have hg_last_lt : g_last < n_max := by dsimp only [g_last, e_plast, u]; rw [henslabs]; omega
  have hg_del_lt : g_del < n_max := by omega
  obtain ⟨hres_app, _⟩ := appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
    hw hb_pos hb s htail hr_cap
  have hetnew : e_tnew = gmAt base U V w₀ n_max h_space s.mem 1 := hres_app
  have ht_lt_n : gmAt base U V w₀ n_max h_space s.mem 1 < n_max := by
    have : (gmAt base U V w₀ n_max h_space s.mem 0 - 1) * slabSize n_max ≥ 0 := Nat.zero_le _
    omega
  refine ⟨by omega, htop_idx_lt, h0_idx_lt, by omega, hg_del_lt, hg_last_lt,
    ⟨htail, hb, hr_cap, hb_pos⟩, by omega, by dsimp only [g_tail]; omega, by omega⟩

/-- Under `DemoteStepInv U V w n_max h_space base b k s` (`k < slabSize n_max`,
`gm (gmRIdx b) = k`, `1 ≤ gm (gmQIdx b)`), `demoteStepProg` returns `k + 1` in `memoryCost = 48`
(`memoryCost_demoteStepProg`). It preserves `frontier`, `lmAt`, and memory outside
`[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It copies entry
`u = (slabSize n_max - 1) - k` of the last full slab `p_last = gm 0 - 1` into `p_del =
gm (gmSlabTopIdx b)`, moves the old entry of `p_del` into the new tail slot
`g_tail = (n_max - 1) - gm 1`, and updates `gmAt` to `gmAppendTail n_max gm b`. -/
theorem demoteStepProg_effect {U V w n_max h_space base b k : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : DemoteStepInv U V w n_max h_space base b k s) :
    let gm := gmAt base U V w n_max h_space s.mem
    let qA := quotAt base U w n_max h_space s.mem
    let vA := valAt base U V w n_max h_space s.mem
    let u := (slabSize n_max - 1) - k
    let p_del := gm (gmSlabTopIdx b)
    let p_last := gm 0 - 1
    let g_del := p_del * slabSize n_max + u
    let g_last := p_last * slabSize n_max + u
    let g_tail := (n_max - 1) - gm 1
    let s' := (Memory.spec 0).clientState s
      (demoteStepProg U V w n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (demoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (Function.update qA g_del (qA g_last)) g_tail (qA g_del) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (Function.update vA g_del (vA g_last)) g_tail (vA g_del) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAppendTail n_max gm b := by
  intro gm qA vA u p_del p_last g_del g_last g_tail s'
  obtain ⟨_, htop_idx_lt, h0_idx_lt, _, hg_del_lt, hg_last_lt,
    ⟨htail, hb, hr_cap, _⟩, _, hg_tail_lt, _⟩ := demoteStep_bounds hw ⟨hpre, hb_pos⟩
  have hr_top := clientResult_readGMProg (U := U) (V := V) (w := w) (h_space := h_space)
    (base := base) s htop_idx_lt
  have hr_0 := clientResult_readGMProg (U := U) (V := V) (w := w) (h_space := h_space)
    (base := base) s h0_idx_lt
  have hg_del_lt : g_del < n_max := by
    dsimp only [g_del, p_del, gmSlabTopIdx, gm]
    rwa [← hr_top]
  have hg_last_lt : g_last < n_max := by
    have h' : ((Memory.spec 0).clientResult s
        (readGMProg U V w n_max h_space (base, 0)) - 1) * slabSize n_max + u < n_max :=
      hg_last_lt
    rwa [hr_0] at h'
  let s₁ := (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b))
  obtain ⟨hres_app, hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail hr_cap
  have hg_tail_lt : g_tail < n_max := by
    have h' : (n_max - 1) - (Memory.spec 0).clientResult s
        (appendTailItemProg U V w n_max h_space (base, b)) < n_max := hg_tail_lt
    rwa [hres_app] at h'
  let s₂ := (Memory.spec 0).clientState s₁
    (writeQuotProg U w n_max h_space ((base, g_del), qA g_last))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeQuotProg_effect (U := U) (base := base) (V := V) (h_space := h_space)
      hw hg_del_lt (quotAt_lt _ _ _ _ _ _ _) s₁
  let s₃ := (Memory.spec 0).clientState s₂
    (writeValProg U V w n_max h_space ((base, g_del), vA g_last))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeValProg_effect (U := U) (V := V) (base := base) (h_space := h_space)
      hw hg_del_lt (valAt_lt _ _ _ _ _ _ _ _ : vA g_last < 2 ^ valBits V) s₂
  let s₄ := (Memory.spec 0).clientState s₃
    (writeQuotProg U w n_max h_space ((base, g_tail), qA g_del))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeQuotProg_effect (U := U) (base := base) (V := V) (h_space := h_space)
      hw hg_tail_lt (quotAt_lt _ _ _ _ _ _ _ : qA g_del < 2 ^ quotientBits U n_max) s₃
  let s₅ := (Memory.spec 0).clientState s₄
    (writeValProg U V w n_max h_space ((base, g_tail), vA g_del))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeValProg_effect (U := U) (V := V) (base := base) (h_space := h_space)
      hw hg_tail_lt (valAt_lt _ _ _ _ _ _ _ _ : vA g_del < 2 ^ valBits V) s₄
  have hr_qd := clientResult_readQuotProg (U := U) (w := w) (h_space := h_space)
    (base := base) s hg_del_lt
  have hr_vd := clientResult_readValProg (U := U) (V := V) (w := w) (h_space := h_space)
    (base := base) s hg_del_lt
  have hr_ql := clientResult_readQuotProg (U := U) (w := w) (h_space := h_space)
    (base := base) s hg_last_lt
  have hr_vl := clientResult_readValProg (U := U) (V := V) (w := w) (h_space := h_space)
    (base := base) s hg_last_lt
  dsimp only [g_del, p_del, gmSlabTopIdx, gm, g_last, p_last, u] at hr_qd hr_vd hr_ql hr_vl
  have hres_eq : (Memory.spec 0).clientResult s
      (demoteStepProg U V w n_max h_space ((base, b), k)) = k + 1 := by
    simp only [demoteStepProg, demoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk,
      p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk,
      writeValGenProg_mk, appendTailItemGenProg_mk]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg, hr_top,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg, hr_0,
      StateTransitionSpec.clientResult_bind, clientState_readQuotProg, hr_qd,
      StateTransitionSpec.clientResult_bind, clientState_readValProg, hr_vd,
      StateTransitionSpec.clientResult_bind, clientState_readQuotProg, hr_ql,
      StateTransitionSpec.clientResult_bind, clientState_readValProg, hr_vl]
    simp only [StateTransitionSpec.clientResult_bind]
    rfl
  have hst : s' = s₅ := by
    dsimp only [s']
    simp only [demoteStepProg, demoteStepGenProg, p_slabSizeSubOne_mk, p_slabSize_mk,
      p_nMaxSubOne_mk, readGMGenProg_mk, readQuotGenProg_mk, readValGenProg_mk, writeQuotGenProg_mk,
      writeValGenProg_mk, appendTailItemGenProg_mk]
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg, hr_top,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hr_0,
      StateTransitionSpec.clientState_bind, clientState_readQuotProg, hr_qd,
      StateTransitionSpec.clientState_bind, clientState_readValProg, hr_vd,
      StateTransitionSpec.clientState_bind, clientState_readQuotProg, hr_ql,
      StateTransitionSpec.clientState_bind, clientState_readValProg, hr_vl,
      StateTransitionSpec.clientState_bind, hres_app]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  refine ⟨hres_eq, by rw [hf5, hf4, hf3, hf2, hf1], fun a ha => ?_,
    by rw [hq5, hq4, hq3, hq2, hq1], by rw [hv5, hv4, hv3, hv2, hv1],
    by rw [hl5, hl4, hl3, hl2, hl1], by rw [hg5, hg4, hg3, hg2, hg1]⟩
  rw [hout5 a (by wram_omega [ha]), hout4 a (by wram_omega [ha]), hout3 a (by wram_omega [ha]),
    hout2 a (by wram_omega [ha]), hout1 a (by wram_omega [ha])]

theorem realizes_demoteStepGen :
    Realizes .exact demoteStepGenProg
      (WordEncoding.encode (α := (DictParams × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      DemoteStepGenPre
      (fun _ _ => 0) := by
  realize
    [realizes_readGMGen, realizes_readQuotGen, realizes_writeQuotGen, realizes_readValGen,
      realizes_writeValGen, realizes_appendTailItemGen]
  all_goals (
    rcases d with ⟨⟨dp, d1⟩, d2⟩
    let d := (d1, d2)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [demoteStepGenPre_mk, appendTailItemGenPre_mk, appendTailItemGenProg_mk]
    obtain ⟨hk_le, htop_lt, h0_lt, hnslabs, hgdel, hglast, happ, htnew, hgtail, hk1_le⟩ :=
      demoteStep_bounds hw h.2
  )
  · exact fits_of_le_globalMetaLen h.1 h.2.2 hw hnU hU htop_lt.le
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact htop_lt
  · exact h0_lt
  · exact hk_le
  · exact fits_of_le_max_n_one h.1 hw hnU hU (hgdel.le.trans (le_max_left n_max 1))
  · exact hgdel
  · exact hnslabs
  · exact fits_of_le_max_n_one h.1 hw hnU hU (hglast.le.trans (le_max_left n_max 1))
  · exact hglast
  · exact ⟨h.1, happ⟩
  · exact htnew
  · exact hgtail
  · exact fits_of_le_max_n_one h.1 hw hnU hU hk1_le

/-! ## Section 2: `DemoteArrInv`, `DemoteLoopInv`, and `demoteSlabProg` -/

/-- Array payload invariant at iteration `k ≤ slabSize n_max` of the slab-demotion loop. -/
structure DemoteArrInv {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α)
    (k : ℕ) (gm : ℕ → ℕ) (arr : ℕ → α) : Prop where
  other_slabs : ∀ p < gm₀ 0 - 1, p ≠ gm₀ (gmSlabTopIdx b) → ∀ u < slabSize n_max,
    arr (p * slabSize n_max + u) = arr₀ (p * slabSize n_max + u)
  other_tails : ∀ t < gm₀ 1,
    arr ((n_max - 1) - t) = arr₀ ((n_max - 1) - t)
  rem_del : ∀ u < slabSize n_max - k,
    arr (gm₀ (gmSlabTopIdx b) * slabSize n_max + u) =
      arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + u)
  rem_last : ∀ u < slabSize n_max - k,
    arr ((gm₀ 0 - 1) * slabSize n_max + u) = arr₀ ((gm₀ 0 - 1) * slabSize n_max + u)
  moved_last : gm₀ (gmSlabTopIdx b) < gm₀ 0 - 1 →
    ∀ u, slabSize n_max - k ≤ u → u < slabSize n_max →
      arr (gm₀ (gmSlabTopIdx b) * slabSize n_max + u) =
        arr₀ ((gm₀ 0 - 1) * slabSize n_max + u)
  demoted_tail : ∀ r < k,
    arr ((n_max - 1) - gm (gmTailPtrIdx n_max b r)) =
      arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + (slabSize n_max - 1 - r))

theorem demoteArrInv_zero {α : Type*} (n_max b : ℕ) (gm₀ : ℕ → ℕ) (arr₀ : ℕ → α) :
    DemoteArrInv n_max b gm₀ arr₀ 0 gm₀ arr₀ := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ u h1 h2 => by omega, fun r hr => by omega⟩

theorem demoteArrInv_step {α : Type*} {n_max b k : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hk : k < slabSize n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (h1_ge : gm₀ 1 ≤ gm 1)
    (htop_b : gm (gmSlabTopIdx b) = gm₀ (gmSlabTopIdx b))
    (hr_b : gm (gmRIdx b) = k)
    (hqb_pos : 1 ≤ gm (gmQIdx b))
    (htot : (gm 0 - 1) * slabSize n_max + (slabSize n_max - k) + gm 1 ≤ n_max)
    (harr : DemoteArrInv n_max b gm₀ arr₀ k gm arr) :
    let u_k := (slabSize n_max - 1) - k
    let g_del := gm (gmSlabTopIdx b) * slabSize n_max + u_k
    let g_last := (gm 0 - 1) * slabSize n_max + u_k
    let g_tail := (n_max - 1) - gm 1
    let arr' := Function.update (Function.update arr g_del (arr g_last)) g_tail (arr g_del)
    DemoteArrInv n_max b gm₀ arr₀ (k + 1) (gmAppendTail n_max gm b) arr' := by
  intro u_k g_del g_last g_tail arr'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hu_k_lt : u_k < slabSize n_max - k := by omega
  have hu_k_slab : u_k < slabSize n_max := by omega
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := hslab.top_lt hb (by omega)
  have hgm0_pos : 1 ≤ gm 0 := by omega
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; rw [ite_eq_right hb0, hr_b]; omega
  have ht_cap : gm 1 < maxTailItems n_max := ntails_lt_maxTailItems_of_r_lt hb hr_cap htail
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hb hr_cap ht_cap
  have hle_mul : gm (gmSlabTopIdx b) * slabSize n_max ≤ (gm 0 - 1) * slabSize n_max :=
    Nat.mul_le_mul_right _ (by omega)
  have hg_del_le_last : g_del ≤ g_last := by dsimp only [g_del, g_last]; omega
  have hg_last_le_tail : g_last ≤ g_tail := by omega
  have harr_del : arr g_del = arr₀ (gm₀ (gmSlabTopIdx b) * slabSize n_max + u_k) := by
    dsimp only [g_del]; rw [htop_b]; exact harr.rem_del u_k hu_k_lt
  have harr_last : arr g_last = arr₀ ((gm₀ 0 - 1) * slabSize n_max + u_k) := by
    dsimp only [g_last]; rw [h0]; exact harr.rem_last u_k hu_k_lt
  have harr_ne (a : ℕ) (h1 : a ≠ g_tail) (h2 : a ≠ g_del) : arr' a = arr a := by
    dsimp only [arr']; rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have haddr_inj {p₁ p₂ u₁ u₂ : ℕ} (hu₁ : u₁ < slabSize n_max) (hu₂ : u₂ < slabSize n_max)
      (heq : p₁ * slabSize n_max + u₁ = p₂ * slabSize n_max + u₂) : p₁ = p₂ ∧ u₁ = u₂ := by
    refine ⟨?_, ?_⟩
    · have h1 := congrArg (· / slabSize n_max) heq
      rwa [Nat.mul_comm p₁, Nat.mul_add_div hK_pos, Nat.div_eq_of_lt hu₁, Nat.add_zero,
        Nat.mul_comm p₂, Nat.mul_add_div hK_pos, Nat.div_eq_of_lt hu₂, Nat.add_zero] at h1
    · have h2 := congrArg (· % slabSize n_max) heq
      rwa [Nat.mul_comm p₁, Nat.mul_add_mod, Nat.mod_eq_of_lt hu₁,
        Nat.mul_comm p₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hu₂] at h2
  have hlt_last {p u : ℕ} (hp : p < gm 0 - 1) (hu : u < slabSize n_max) :
      p * slabSize n_max + u < g_last := by
    have := Nat.mul_le_mul_right (slabSize n_max) hp; rw [Nat.add_one_mul] at this; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hp_ne u hu
    have := hlt_last (h0 ▸ hp) hu
    rw [harr_ne _ (by omega) (fun heq => hp_ne (by
      have := (haddr_inj hu hu_k_slab heq).1; rw [← htop_b, this]))]
    exact harr.other_slabs p hp hp_ne u hu
  · intro t ht
    rw [harr_ne _ (by omega) (by omega)]
    exact harr.other_tails t ht
  · intro u hu
    rw [harr_ne _ (by rw [← htop_b]; omega) (by dsimp only [g_del]; rw [htop_b]; omega)]
    exact harr.rem_del u (by omega)
  · intro u hu
    rw [harr_ne _ (by rw [← h0]; dsimp only [g_last] at *; omega) (fun heq => by
      have := (haddr_inj (by omega) hu_k_slab heq).2; omega)]
    exact harr.rem_last u (by omega)
  · intro hp_lt_last u hu_ge hu_lt
    have := hlt_last (h0 ▸ hp_lt_last) hu_lt
    dsimp only [arr']
    rw [Function.update_of_ne (by omega)]
    by_cases hueq : u = u_k
    · subst hueq
      rw [show gm₀ (gmSlabTopIdx b) * slabSize n_max + u_k = g_del by
          dsimp only [g_del]; rw [htop_b],
        Function.update_self, harr_last]
    · rw [Function.update_of_ne (by dsimp only [g_del]; rw [htop_b]; omega)]
      exact harr.moved_last hp_lt_last u (by omega) hu_lt
  · intro r hr
    have hr_cap' : r < tailCapPerBucket n_max := by
      unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
    have hd_lt : b * tailCapPerBucket n_max + r < maxTailItems n_max :=
      mul_tailCapPerBucket_add_lt_maxTailItems hb hr_cap'
    rw [gmTailPtrIdx, hptr_val _ hd_lt]
    by_cases hreq : r = k
    · subst hreq
      rw [ite_eq_left (by rw [hr_b])]
      dsimp only [arr', g_tail]; rw [Function.update_self, harr_del]
    · rw [ite_eq_right (by rw [hr_b]; omega), ← gmTailPtrIdx]
      have ht_r_lt := htail.ptr_lt b hb r (by rw [hr_b]; omega)
      rw [harr_ne _ (by omega) (by omega)]
      exact harr.demoted_tail r (by omega)

/-- Full loop invariant for `k ≤ slabSize n_max` iterations of `demoteStepProg` starting from
`s₀`. -/
structure DemoteLoopInv (U V w₀ n_max h_space base b : ℕ) (s₀ : Memory.State)
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
  gm1_eq : gmAt base U V w₀ n_max h_space s.mem 1 = gmAt base U V w₀ n_max h_space s₀.mem 1 + k
  rb_eq : gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) = k
  qb_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmQIdx b)
  top_b_eq : gmAt base U V w₀ n_max h_space s.mem (gmSlabTopIdx b) =
    gmAt base U V w₀ n_max h_space s₀.mem (gmSlabTopIdx b)
  r_other : ∀ b' < numBuckets n_max, b' ≠ b →
    gmAt base U V w₀ n_max h_space s.mem (gmRIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b')
  q_eq : ∀ b' < numBuckets n_max,
    gmAt base U V w₀ n_max h_space s.mem (gmQIdx b') =
      gmAt base U V w₀ n_max h_space s₀.mem (gmQIdx b')
  slabPtr_eq : ∀ b' s_idx,
    slabPtrOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' s_idx =
      slabPtrOf n_max (gmAt base U V w₀ n_max h_space s₀.mem) b' s_idx
  tail_other : ∀ b' < numBuckets n_max, b' ≠ b →
    ∀ r < gmAt base U V w₀ n_max h_space s₀.mem (gmRIdx b'),
      gmAt base U V w₀ n_max h_space s.mem (gmTailPtrIdx n_max b' r) =
        gmAt base U V w₀ n_max h_space s₀.mem (gmTailPtrIdx n_max b' r)
  tot_le : (gmAt base U V w₀ n_max h_space s.mem 0 - 1) * slabSize n_max +
    (slabSize n_max - k) + gmAt base U V w₀ n_max h_space s.mem 1 ≤ n_max
  quot_inv : DemoteArrInv n_max b
    (gmAt base U V w₀ n_max h_space s₀.mem) (quotAt base U w₀ n_max h_space s₀.mem)
    k (gmAt base U V w₀ n_max h_space s.mem) (quotAt base U w₀ n_max h_space s.mem)
  val_inv : DemoteArrInv n_max b
    (gmAt base U V w₀ n_max h_space s₀.mem) (valAt base U V w₀ n_max h_space s₀.mem)
    k (gmAt base U V w₀ n_max h_space s.mem) (valAt base U V w₀ n_max h_space s.mem)

theorem demoteLoopInv_to_stepInv {U V w₀ n_max h_space base b k : ℕ}
    {s₀ s : Memory.State}
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s)
    (hk : k < slabSize n_max) :
    DemoteStepInv U V w₀ n_max h_space base b k s :=
  ⟨hloop.b_lt, hk, hloop.tail_bij, hloop.slab_bij, hloop.rb_eq, hloop.qb_pos, hloop.tot_le⟩

theorem demoteLoopInv_step {U V w₀ n_max h_space base b k : ℕ}
    {s₀ s : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s)
    (hk : k < slabSize n_max) :
    let s' := (Memory.spec 0).clientState s
      (demoteStepProg U V w₀ n_max h_space ((base, b), k))
    (Memory.spec 0).clientResult s
      (demoteStepProg U V w₀ n_max h_space ((base, b), k)) = k + 1 ∧
    DemoteLoopInv U V w₀ n_max h_space base b s₀ (k + 1) s' := by
  intro s'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  obtain ⟨hres, hf, hout, hq, hv, hl, hgm⟩ :=
    demoteStepProg_effect hw hb_pos s (demoteLoopInv_to_stepInv hloop hk)
  let gm := gmAt base U V w₀ n_max h_space s.mem
  let gm₀ := gmAt base U V w₀ n_max h_space s₀.mem
  have hr_cap : gm (gmRIdx b) < tailCapPerBucket n_max := by
    unfold tailCapPerBucket; dsimp only [gm]; rw [ite_eq_right hb0, hloop.rb_eq]; omega
  have ht_cap : gm 1 < maxTailItems n_max :=
    ntails_lt_maxTailItems_of_r_lt hloop.b_lt hr_cap hloop.tail_bij
  obtain ⟨h0', h1', hrb', hr_other', hq', htop', -⟩ :=
    gmAppendTail_preserves_nonTail gm hloop.b_lt hr_cap ht_cap
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hloop.b_lt hr_cap ht_cap
  obtain ⟨hptr_slab, hslab'⟩ := slabBijection_gmAppendTail hloop.b_lt hr_cap ht_cap hloop.slab_bij
  have h1_ge : gm₀ 1 ≤ gm 1 := by have := hloop.gm1_eq; dsimp only [gm, gm₀]; omega
  have hq_inv' := demoteArrInv_step hb_pos hloop.b_lt hk hloop.tail_bij hloop.slab_bij
    hloop.gm0_eq h1_ge hloop.top_b_eq hloop.rb_eq hloop.qb_pos hloop.tot_le hloop.quot_inv
  have hv_inv' := demoteArrInv_step hb_pos hloop.b_lt hk hloop.tail_bij hloop.slab_bij
    hloop.gm0_eq h1_ge hloop.top_b_eq hloop.rb_eq hloop.qb_pos hloop.tot_le hloop.val_inv
  refine ⟨hres, hloop.b_lt, by omega, by rw [hf, hloop.frontier_eq],
    fun a ha => by rw [hout a ha, hloop.mem_out a ha], by rw [hl, hloop.lm_eq],
    by rw [hgm]; exact tailBijection_gmAppendTail hloop.b_lt hr_cap ht_cap hloop.tail_bij,
    by rw [hgm]; exact hslab',
    by rw [hgm, h0']; exact hloop.gm0_eq,
    by rw [hgm, h1']; dsimp only [gm, gm₀] at *; rw [hloop.gm1_eq]; omega,
    by rw [hgm, hrb']; dsimp only [gm]; rw [hloop.rb_eq],
    by rw [hgm, hq' b hloop.b_lt]; exact hloop.qb_pos,
    by rw [hgm, htop' b hloop.b_lt]; exact hloop.top_b_eq,
    fun b' hb' hne => by rw [hgm, hr_other' b' hb' hne]; exact hloop.r_other b' hb' hne,
    fun b' hb' => by rw [hgm, hq' b' hb']; exact hloop.q_eq b' hb',
    fun b' s_idx => by rw [hgm, hptr_slab]; exact hloop.slabPtr_eq b' s_idx,
    fun b' hb' hne r hr => ?_,
    by rw [hgm, h0', h1']; have := hloop.tot_le; dsimp only [gm] at *; omega,
    by rw [hgm, hq]; exact hq_inv', by rw [hgm, hv]; exact hv_inv'⟩
  have hr_cap' : r < tailCapPerBucket n_max :=
    lt_of_lt_of_le (hloop.r_other b' hb' hne ▸ hr) (hloop.tail_bij.r_le b' hb')
  have hd_ne : b' * tailCapPerBucket n_max + r ≠ b * tailCapPerBucket n_max + gm (gmRIdx b) :=
    fun heq => hne (flat_descriptor_inj hr_cap' hr_cap heq).1
  rw [hgm, gmTailPtrIdx, hptr_val _ (mul_tailCapPerBucket_add_lt_maxTailItems hb' hr_cap'),
    ite_eq_right hd_ne, ← gmTailPtrIdx]
  exact hloop.tail_other b' hb' hne r hr

/-- Parameter-free `Memory.Prog` loop executing `n` iterations of `demoteStepGenProg` starting
from index `k`: `d = (((dp, (base, b)), k), n)`. -/
def demoteLoopGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate demoteStepGenProg d.1.1 d.2 d.1.2

/-- `Memory.Prog` loop executing `n` iterations of `demoteStepProg` starting from index `k`:
`d = (((base, b), k), n)`. -/
def demoteLoopProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  iterate (demoteStepProg U V w n_max h_space) d.1.1 d.2 d.1.2

@[simp] theorem iterate_demoteStepGenProg_mk (U V w n_max h_space : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) :
    iterate demoteStepGenProg (mkDictParams U V w n_max h_space, d) m k =
      iterate (demoteStepProg U V w n_max h_space) d m k :=
  iterate_congr (fun a => demoteStepGenProg_mk U V w n_max h_space d a) m k

@[simp] theorem demoteLoopGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    demoteLoopGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      demoteLoopProg U V w n_max h_space ((d1, d2), d3) :=
  iterate_demoteStepGenProg_mk U V w n_max h_space d1 d3 d2

@[simp] theorem iterationSafe_demoteStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (d : ℕ × ℕ) (m k : ℕ) (s : Memory.State) :
    iterationSafe demoteStepGenProg DemoteStepGenPre w
        (mkDictParams U V w₀ n_max h_space, d) m k s ↔
      iterationSafe (demoteStepProg U V w₀ n_max h_space)
        (fun w x s => DemoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w d m k s :=
  iterationSafe_congr (fun a => demoteStepGenProg_mk U V w₀ n_max h_space d a)
    (fun a t => demoteStepGenPre_mk U V w₀ n_max h_space w d a t) m k s

theorem iterate_demoteStepProg_spec {U V w₀ n_max h_space base b w : ℕ} {s₀ : Memory.State}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (n k : ℕ) (s : Memory.State)
    (hnk : k + n ≤ slabSize n_max)
    (hloop : DemoteLoopInv U V w₀ n_max h_space base b s₀ k s) :
    let prog := iterate (demoteStepProg U V w₀ n_max h_space) (base, b) n k
    DemoteLoopInv U V w₀ n_max h_space base b s₀ (k + n)
      ((Memory.spec 0).clientState s prog) ∧
    memoryCost prog s = 48 * n ∧
    (DictEnvGen w (mkDictParams U V w₀ n_max h_space) base →
      iterationSafe (demoteStepProg U V w₀ n_max h_space)
        (fun w x s => DemoteStepPre U V w₀ n_max h_space w x.1.1 x.1.2 x.2 s)
        w (base, b) n k s) := by
  induction n generalizing k s with
  | zero =>
    simp only [iterate, Nat.add_zero, memoryCost_pure, Nat.mul_zero, iterationSafe]
    exact ⟨hloop, trivial, fun _ => trivial⟩
  | succ n ih =>
    have hk : k < slabSize n_max := by omega
    obtain ⟨hres, hloop'⟩ := demoteLoopInv_step hw hb_pos hloop hk
    let s' := (Memory.spec 0).clientState s (demoteStepProg U V w₀ n_max h_space ((base, b), k))
    obtain ⟨hfinal, hcost', hsafe'⟩ := ih (k + 1) s' (by omega) hloop'
    rw [show k + 1 + n = k + (n + 1) by omega] at hfinal
    refine ⟨?_, ?_, fun hdict => ?_⟩
    · simp only [iterate]
      rw [StateTransitionSpec.clientState_bind, hres]
      exact hfinal
    · simp only [iterate, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_demoteStepProg, hres]
      change 48 + memoryCost
        (iterate (demoteStepProg U V w₀ n_max h_space) (base, b) n (k + 1)) s' = 48 * (n + 1)
      rw [hcost']; omega
    · simp only [iterationSafe, hres]
      exact ⟨⟨hdict, demoteLoopInv_to_stepInv hloop hk, hb_pos⟩, hsafe' hdict⟩

theorem realizes_demoteLoopGen :
    Realizes .exact demoteLoopGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s =>
        iterationSafe demoteStepGenProg DemoteStepGenPre w d.1.1 d.2 d.1.2 s)
      (fun _ _ => 0) :=
  Realizes.iterate₀ (WordEncoding.encode (α := DictParams × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_demoteStepGen
    one_le_memoryCost_demoteStepGenProg

/-- Parameter-free `Memory.Prog` operation demoting the top full slab of bucket `b = d.2.2` at
`base = d.2.1` into `K = slabSize n_max` tail items. -/
@[expose]
def demoteSlabGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let _ ← demoteLoopGenProg ((d, 0), dpSlabSize d.1)
  gmPopSlabGenProg d

/-- `Memory.Prog` operation demoting the top full slab of bucket `b = d.2` at `base = d.1`
(`gm (gmRIdx b) = 0`, `1 ≤ gm (gmQIdx b)`) into `K = slabSize n_max` tail items via
`demoteLoopProg` followed by `gmPopSlabProg`. -/
@[expose]
def demoteSlabProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit :=
  demoteSlabGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem demoteSlabGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    demoteSlabGenProg (mkDictParams U V w n_max h_space, d) =
      demoteSlabProg U V w n_max h_space d := by
  rfl

/-- Pure entry invariant for `demoteSlabProg`. -/
@[expose]
def DemoteSlabInv (U V w₀ n_max h_space base b : ℕ) (s : Memory.State) : Prop :=
  let gm := gmAt base U V w₀ n_max h_space s.mem
  b < numBuckets n_max ∧
  TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0) ∧
  gm (gmRIdx b) = 0 ∧
  1 ≤ gm (gmQIdx b) ∧
  (∀ b' < numBuckets n_max, b' ≠ b →
    gm (gmRIdx b') < tailCapPerBucket n_max ∧
    (0 < gm (gmQIdx b') → 1 ≤ gm (gmRIdx b'))) ∧
  gm 0 * slabSize n_max + gm 1 ≤ n_max

/-- Precondition for `demoteSlabProg` in `Realizes`. -/
@[expose]
def DemoteSlabPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  DemoteSlabInv U V w₀ n_max h_space base b s ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `demoteSlabGenProg`. -/
@[expose]
def DemoteSlabGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  DemoteSlabInv (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) d.2.1 d.2.2 s ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem demoteSlabGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    DemoteSlabGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      DemoteSlabPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

theorem demoteLoopInv_zero {U V w₀ n_max h_space base b : ℕ} {s₀ : Memory.State}
    (hpre : DemoteSlabInv U V w₀ n_max h_space base b s₀) :
    DemoteLoopInv U V w₀ n_max h_space base b s₀ 0 s₀ := by
  rcases hpre with ⟨hb, htail, hslab, hrb, hqb_pos, _, htot⟩
  set gm₀ := gmAt base U V w₀ n_max h_space s₀.mem
  have hp_del_lt := hslab.top_lt hb (by omega)
  have htot' : (gm₀ 0 - 1) * slabSize n_max + (slabSize n_max - 0) + gm₀ 1 ≤ n_max := by
    rw [Nat.sub_zero, ← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]; exact htot
  refine ⟨hb, Nat.zero_le _, rfl, fun _ _ => rfl, rfl, htail, hslab, rfl,
    (Nat.add_zero _).symm, hrb, hqb_pos, rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl, htot',
    demoteArrInv_zero _ _ _ _, demoteArrInv_zero _ _ _ _⟩

theorem slotOf_gmPopSlab_preserve {α : Type*} {n_max b : ℕ} {gm₀ gm : ℕ → ℕ} {arr₀ arr : ℕ → α}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (htail₀ : TailBijection n_max gm₀ (fun b' => gm₀ (gmRIdx b')) (gm₀ 1))
    (_htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab₀ : SlabBijection n_max gm₀ (fun b' => gm₀ (gmQIdx b')) (gm₀ 0))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (h0 : gm 0 = gm₀ 0)
    (hq : ∀ b' < numBuckets n_max, gm (gmQIdx b') = gm₀ (gmQIdx b'))
    (htop_b : gm (gmSlabTopIdx b) = gm₀ (gmSlabTopIdx b))
    (hr_other : ∀ b' < numBuckets n_max, b' ≠ b → gm (gmRIdx b') = gm₀ (gmRIdx b'))
    (hr_b : gm (gmRIdx b) = slabSize n_max)
    (_hr0_b : gm₀ (gmRIdx b) = 0)
    (hqb_pos : 1 ≤ gm₀ (gmQIdx b))
    (hslabPtr : ∀ b' s_idx, slabPtrOf n_max gm b' s_idx = slabPtrOf n_max gm₀ b' s_idx)
    (htail_other : ∀ b' < numBuckets n_max, b' ≠ b → ∀ r < gm₀ (gmRIdx b'),
      gm (gmTailPtrIdx n_max b' r) = gm₀ (gmTailPtrIdx n_max b' r))
    (harr : DemoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm arr) :
    ∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmPopSlab n_max gm b) b',
      arr (slotOf n_max (gmPopSlab n_max gm b) b' j) = arr₀ (slotOf n_max gm₀ b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  have hqb_pos' : 1 ≤ gm (gmQIdx b) := by rw [hq b hb]; exact hqb_pos
  obtain ⟨-, -, hfr, hfq, hftail⟩ := gmPopSlab_preserves_tail hb hslab
  obtain ⟨hptr, _⟩ := slabBijection_gmPopSlab hb hqb_pos' hslab
  have htop_eq0 := hslab₀.top_eq b hb (gm₀ (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt0 := hslab₀.top_lt hb (by omega)
  have hmul : gm₀ (gmQIdx b) * slabSize n_max =
      (gm₀ (gmQIdx b) - 1) * slabSize n_max + slabSize n_max := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hqb_pos]
  intro b' hb' j hj
  unfold bCount at hj
  simp only [hb0, ↓reduceIte, hb'] at hj
  unfold slotOf
  rw [ite_eq_right hb0, ite_eq_right hb0]
  by_cases hj_slab : j < gmPopSlab n_max gm b (gmQIdx b') * slabSize n_max <;>
    by_cases hj_slab0 : j < gm₀ (gmQIdx b') * slabSize n_max <;>
    simp only [hj_slab, hj_slab0, ↓reduceIte]
  · have hs_lt : j / slabSize n_max < gmPopSlab n_max gm b (gmQIdx b') :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hs_lt0 : j / slabSize n_max < gm₀ (gmQIdx b') :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hu_lt : slabSize n_max - 1 - j % slabSize n_max < slabSize n_max := by
      have := Nat.mod_lt j hK_pos; omega
    have hne_top : ¬(b' = b ∧ j / slabSize n_max = gm₀ (gmQIdx b) - 1) := by
      rintro ⟨rfl, _⟩
      rw [hfq b' hb', ite_eq_left rfl, hq b' hb'] at hs_lt
      omega
    have hp_ne_del : slabPtrOf n_max gm₀ b' (j / slabSize n_max) ≠ gm₀ (gmSlabTopIdx b) := by
      intro heq
      rw [htop_eq0] at heq
      exact hne_top
        ⟨(hslab₀.ownerB_ptr b' hb' (j / slabSize n_max) hs_lt0).symm.trans
          (by rw [heq]; exact hslab₀.ownerB_ptr b hb (gm₀ (gmQIdx b) - 1) (by omega)),
        (hslab₀.ownerS_ptr b' hb' (j / slabSize n_max) hs_lt0).symm.trans
          (by rw [heq]; exact hslab₀.ownerS_ptr b hb (gm₀ (gmQIdx b) - 1) (by omega))⟩
    rw [hptr b' hb' (j / slabSize n_max) hs_lt, hslabPtr, h0, htop_b]
    split_ifs with hp_last
    · rw [hp_last]
      exact harr.moved_last (by rw [hp_last] at hp_ne_del; omega) _ (by omega) hu_lt
    · have := hslab₀.ptr_lt b' hb' (j / slabSize n_max) hs_lt0
      exact harr.other_slabs _ (by omega) hp_ne_del _ hu_lt
  · rw [hfq b' hb'] at hj_slab
    have hle := Nat.mul_le_mul_right (slabSize n_max)
      (show gm₀ (gmQIdx b') - 1 ≤ gm₀ (gmQIdx b') by omega)
    split_ifs at hj_slab with hbeq <;> [subst hbeq; skip] <;> rw [hq b' hb'] at hj_slab <;> omega
  · by_cases hbeq : b' = b
    · subst hbeq
      rw [hfq b' hb', ite_eq_left rfl, hq b' hb'] at hj_slab hj ⊢
      rw [hfr b' hb', hr_b] at hj
      set r := j - (gm₀ (gmQIdx b') - 1) * slabSize n_max
      have hr_lt : r < slabSize n_max := by omega
      have hr_cap : r < tailCapPerBucket n_max := by
        unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
      have hd_lt := mul_tailCapPerBucket_add_lt_maxTailItems hb' hr_cap
      rw [hftail _ (by wram_omega) (by wram_omega), harr.demoted_tail r hr_lt, htop_eq0,
        show j / slabSize n_max = gm₀ (gmQIdx b') - 1 by
          rw [show j = (gm₀ (gmQIdx b') - 1) * slabSize n_max + r by omega, Nat.mul_comm,
            Nat.mul_add_div hK_pos, Nat.div_eq_of_lt hr_lt, Nat.add_zero],
        show j % slabSize n_max = r by
          rw [show j = (gm₀ (gmQIdx b') - 1) * slabSize n_max + r by omega, Nat.mul_comm,
            Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]]
    · exfalso
      rw [hfq b' hb', ite_eq_right hbeq, hq b' hb'] at hj_slab
      exact hj_slab hj_slab0
  · by_cases hbeq : b' = b
    · subst hbeq
      rw [hfq b' hb', ite_eq_left rfl, hfr b' hb', hq b' hb', hr_b] at hj
      omega
    · rw [hfq b' hb', ite_eq_right hbeq, hq b' hb'] at hj_slab hj ⊢
      rw [hfr b' hb', hr_other b' hb' hbeq] at hj
      set r := j - gm₀ (gmQIdx b') * slabSize n_max
      have hr_lt : r < gm₀ (gmRIdx b') := by omega
      have hd_lt := mul_tailCapPerBucket_add_lt_maxTailItems hb'
        (lt_of_lt_of_le hr_lt (htail₀.r_le b' hb'))
      rw [hftail _ (by wram_omega) (by wram_omega), htail_other b' hb' hbeq r hr_lt]
      exact harr.other_tails _ (htail₀.ptr_lt b' hb' r hr_lt)

/-- Under `DemoteSlabInv U V w n_max h_space base b s` (`gm (gmRIdx b) = 0` and
`1 ≤ gm (gmQIdx b)`), `demoteSlabProg` runs in `memoryCost ≤ 48 * slabSize n_max + 68` and preserves
`frontier`, `lmAt`, and memory outside
`[base + offQuot h_space, base + totalSpace U V w n_max h_space)`. It restores
`SlotStoreInv n_max gm'` with `gm' (gmQIdx b) = gm₀ (gmQIdx b) - 1`,
`gm' (gmRIdx b) = slabSize n_max`, and unchanged `(gmQIdx b', gmRIdx b')` for `b' ≠ b`. It also
preserves `bCount` and every logical `(quotAt, valAt)` entry at `slotOf` across all buckets. -/
theorem demoteSlabProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hpre : DemoteSlabInv U V w n_max h_space base b s) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    gm' (gmQIdx b) = gm₀ (gmQIdx b) - 1 ∧
    gm' (gmRIdx b) = slabSize n_max ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s ≤
      48 * slabSize n_max + 68 := by
  intro gm₀ s' gm'
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
  obtain ⟨hloopK, hcost_loop, _⟩ :=
    iterate_demoteStepProg_spec (w := w) hw hb_pos (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero hpre)
  rw [Nat.zero_add] at hloopK
  rcases hpre with ⟨hb, htail₀, hslab₀, hrb₀, hqb₀, hother₀, -⟩
  set s₁ := (Memory.spec 0).clientState s
    (demoteLoopProg U V w n_max h_space (((base, b), 0), slabSize n_max))
  change DemoteLoopInv U V w n_max h_space base b s (slabSize n_max) s₁ at hloopK
  obtain ⟨hf_pop, hout_pop, hq_pop, hv_pop, hl_pop, hgm_pop⟩ :=
    gmPopSlabProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hloopK.b_lt s₁ hloopK.slab_bij hloopK.qb_pos
  have hst : s' =
      (Memory.spec 0).clientState s₁ (gmPopSlabProg U V w n_max h_space (base, b)) := by
    change (Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b)) = _
    simp only [demoteSlabProg, demoteSlabGenProg, p_slabSize_mk, demoteLoopGenProg_mk,
      gmPopSlabGenProg_mk]
    rw [StateTransitionSpec.clientState_bind]
  let gm₁ := gmAt base U V w n_max h_space s₁.mem
  have hgm'_eq : gm' = gmPopSlab n_max gm₁ b := by dsimp only [gm']; rw [hst, hgm_pop]
  obtain ⟨hf0, hf1, hfr, hfq, -⟩ := gmPopSlab_preserves_tail hloopK.b_lt hloopK.slab_bij
  obtain ⟨_, hslab2⟩ := slabBijection_gmPopSlab hloopK.b_lt hloopK.qb_pos hloopK.slab_bij
  have htail2 := tailBijection_gmPopSlab hloopK.b_lt hloopK.slab_bij hloopK.tail_bij
  have hqb : gm' (gmQIdx b) = gm₀ (gmQIdx b) - 1 := by
    rw [hgm'_eq, hfq b hloopK.b_lt, ite_eq_left rfl, hloopK.q_eq b hloopK.b_lt]
  have hrb : gm' (gmRIdx b) = slabSize n_max := by
    rw [hgm'_eq, hfr b hloopK.b_lt]; exact hloopK.rb_eq
  have hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := fun b' hb' hne => by
    rw [hgm'_eq, hfq b' hb', ite_eq_right hne, hfr b' hb']
    exact ⟨hloopK.q_eq b' hb', hloopK.r_other b' hb' hne⟩
  have hinv2 : SlotStoreInv n_max gm' := by
    refine ⟨fun _ => by omega, fun _ => by rw [hgm'_eq]; exact htail2,
      fun _ => by rw [hgm'_eq]; exact hslab2, fun _ b' hb' => ?_,
      fun _ => by rw [hgm'_eq, hf0, hf1]; have := hloopK.tot_le; omega⟩
    by_cases hbeq : b' = b
    · subst b'; rw [hrb]; unfold tailCapPerBucket; rw [ite_eq_right hb0]; omega
    · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]; exact hother₀ b' hb' hbeq
  have hbc : ∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₀ b' := fun b' hb' => by
    unfold bCount; simp only [hb0, ↓reduceIte, hb']
    by_cases hbeq : b' = b
    · subst b'; rw [hqb, hrb]; dsimp only [gm₀]
      rw [hrb₀, Nat.add_zero, ← Nat.add_one_mul, Nat.sub_add_cancel hqb₀]
    · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
  have hslot {arr₀ arr : ℕ → ℕ}
      (harr : DemoteArrInv n_max b gm₀ arr₀ (slabSize n_max) gm₁ arr) :=
    slotOf_gmPopSlab_preserve hb_pos hloopK.b_lt htail₀ hloopK.tail_bij
      hslab₀ hloopK.slab_bij hloopK.gm0_eq hloopK.q_eq hloopK.top_b_eq hloopK.r_other
      hloopK.rb_eq hrb₀ hqb₀ hloopK.slabPtr_eq hloopK.tail_other harr
  refine ⟨by rw [hst, hf_pop, hloopK.frontier_eq],
    fun a ha => by rw [hst, hout_pop a (by wram_omega [ha]), hloopK.mem_out a ha],
    by rw [hst, hl_pop, hloopK.lm_eq], hinv2, hqb, hrb, hother, hbc,
    fun b' hb' j hj => ?_, ?_⟩
  · rw [hst, hq_pop, hv_pop, hgm'_eq]; rw [hgm'_eq] at hj
    exact ⟨hslot hloopK.quot_inv b' hb' j hj, hslot hloopK.val_inv b' hb' j hj⟩
  · simp only [demoteSlabProg, demoteSlabGenProg, p_slabSize_mk,
      demoteLoopGenProg_mk, gmPopSlabGenProg_mk]
    unfold demoteLoopProg
    rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    change memoryCost
        (iterate (demoteStepProg U V w n_max h_space) (base, b) (slabSize n_max) 0) s +
      memoryCost (gmPopSlabProg U V w n_max h_space (base, b)) s₁ ≤ _
    rw [hcost_loop]
    have := memoryCost_gmPopSlabProg_le U V w n_max h_space (base, b) s₁
    omega

theorem realizes_demoteSlabGen :
    Realizes .exact demoteSlabGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      DemoteSlabGenPre
      (fun _ _ => 0) := by
  have hloop := realizes_demoteLoopGen
  have hpop := realizes_gmPopSlabGen
  realizeDictWith [demoteSlabGenPre_mk, iterationSafe_demoteStepGenProg_mk,
    demoteLoopGenProg_mk, gmPopSlabGenPre_mk, gmPopSlabGenProg_mk]
  · exact (iterate_demoteStepProg_spec hw h.2.2 (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero h.2.1)).2.2 h.1
  · rcases d with ⟨base, b⟩
    dsimp only at h
    have hloopK := (iterate_demoteStepProg_spec (w := w) hw h.2.2 (slabSize n_max) 0 s
      (by omega) (demoteLoopInv_zero h.2.1)).1
    rw [Nat.zero_add] at hloopK
    exact ⟨h.1, hloopK.slab_bij, h.2.1.1, hloopK.qb_pos, h.2.2⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
