/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch

/-!
# Ghost `DictEnvGen`, `CompEpochEnv`, `FixedCoupled` Bridges, and `CompGmFrame`

Provides ghost fixed-capacity envelope certificates at `(base = 0, ghostW w)`, the concrete epoch
envelope `CompEpochEnv`, `FixedCoupled` dense-to-physical lookup and in-place value-update bridges,
and the `GlobalMeta`-only frame relation `CompGmFrame` with generic `ValidProg` bind helpers.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompEpochEnv`:
  concrete parameter and frontier envelope covering compacted metadata and `m_items` dense slots.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompGmFrame`:
  frame relation for operations modifying only the compacted `GlobalMeta` slice.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ghostDictParamsWf`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ghostDictEnvGen`:
  unconditional `DictParamsWf` and `DictEnvGen` certificates at `(0, ghostW w)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.tailDenseInv`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.denseOfPhysPre_slotOf`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.quot_val_at_slotOf`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.FixedCoupled.writeVal_slotOf`:
  dense-to-physical lookup and in-place value-update bridges under `FixedCoupled`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compGmFrame_writeCompGMGenProg`:
  `CompGmFrame` and `compGmAt` update law for `writeCompGMGenProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_bind_unit`,
  `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.validProg_bind_of_eq`:
  generic `ValidProg w 0` bind combinators.
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

private theorem packedWords_le_len_add_two {len k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) :
    packedWords len k w ≤ len + 2 := by
  unfold packedWords
  have hle : len * k + w - 1 ≤ (w - 1) + len * w := by
    have := Nat.mul_le_mul_left len hkw; omega
  calc (len * k + w - 1) / w + 2
      ≤ ((w - 1) + len * w) / w + 2 := Nat.add_le_add_right (Nat.div_le_div_right hle) 2
    _ = (w - 1) / w + len + 2 := by rw [Nat.add_mul_div_right _ _ hw]
    _ = len + 2 := by rw [Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]

/-- At ghost word width `ghostW w = w + 16`, `DictParamsWf U V (ghostW w) N` holds for all
`N ≤ U < 2 ^ w` and `V ≤ 2 ^ w`. -/
theorem ghostDictParamsWf {U V w N : ℕ} (_hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hV : V ≤ 2 ^ w) :
    DictParamsWf U V (ghostW w) N := by
  have hpow : 2 ^ w ≤ 2 ^ ghostW w := Nat.pow_le_pow_right two_pos (by unfold ghostW; omega)
  exact ⟨by unfold ghostW; omega, hnU, lt_of_lt_of_le hU hpow, hV.trans hpow⟩

/-- At `base = 0` and `ghostW w = w + 16`, `DictEnvGen` holds unconditionally for any
`0 < w`, `N ≤ U < 2 ^ w`, and `V ≤ 2 ^ w` (`totalSpace < 2 ^ (w + 16)`). -/
theorem ghostDictEnvGen {U V w N : ℕ} (hw : 0 < w) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hV : V ≤ 2 ^ w) :
    DictEnvGen (ghostW w) (mkDictParams U V (ghostW w) N (hashSpace U (ghostW w) N)) 0 := by
  have hwf := ghostDictParamsWf hw hnU hU hV
  refine ⟨⟨U, V, ghostW w, N, hashSpace U (ghostW w) N, hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2,
    rfl⟩, rfl, ?_⟩
  simp only [p_U_mk, p_V_mk, p_w_mk, p_nMax_mk, p_hSpace_mk, Nat.zero_add]
  set wg := ghostW w
  have hwg : 0 < wg := hwf.1
  have hh := hashSpace_le hwg hnU hwf.2.2.1.le
  have hq : packedWords N (quotientBits U N) wg ≤ N + 2 :=
    packedWords_le_len_add_two hwg (quotientBits_le_of_le_pow hwf.2.2.1.le)
  have hv : packedWords N (valBits V) wg ≤ N + 2 :=
    packedWords_le_len_add_two hwg (Nat.clog_le_of_le_pow hwf.2.2.2)
  have hlm_sub : lmSubWords N wg ≤ max N 1 + 2 :=
    (packedWords_le_len_add_two hwg (effBucketPosBits_le_of_lt_pow hnU hwf.2.2.1)).trans
      (Nat.add_le_add_right (totalMicroBuckets_le N) 2)
  have hgm_len : globalMetaLen N ≤ max N 1 + 7 := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · unfold globalMetaLen globalMetaVarLen; simp [hb0]
    · have := globalMetaLen_le_of_bucketBits_pos hb_pos; omega
  have hgm : packedWords (globalMetaLen N) (globalPtrBits N) wg ≤ max N 1 + 9 :=
    (packedWords_le_len_add_two hwg (globalPtrBits_le_of_lt_pow hnU hwf.2.2.1)).trans
      (by omega)
  have hob : packedWords (2 * N) 1 wg ≤ 2 * N + 2 :=
    packedWords_le_len_add_two hwg hwg
  have hmax_lt : max N 1 < 2 ^ w := max_n_one_lt_two_pow_w hw hnU hU
  have h2w_pos : 2 ≤ 2 ^ w := Nat.le_self_pow hw.ne' 2
  have hpow16 : 2 ^ ghostW w = 2 ^ w * 65536 := by
    unfold ghostW; rw [Nat.pow_add]
  change totalSpace U V wg N (hashSpace U wg N) < 2 ^ ghostW w
  rw [hpow16]
  unfold totalSpace offGM offLM offVal offQuot
  omega

/-- Extract `TailDenseInv` from `FixedCoupled`. -/
theorem FixedCoupled.tailDenseInv {metaBase itemBase U V w N : ℕ} {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s) (hb_pos : 0 < bucketBits N) :
    TailDenseInv N (compGmAt metaBase U w N s.mem 0) (compGmAt metaBase U w N s.mem 1)
      (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem) := by
  have hwin := hcpl.win_inv
  simp only [hb_pos.ne', ↓reduceIte] at hwin
  exact hwin

/-- Concrete epoch parameter and frontier envelope at `(metaBase, itemBase)` covering `m_items`
dense `(quotient, value)` slots. -/
structure CompEpochEnv (U V w N metaBase itemBase m_items : ℕ) (s : Memory.State) : Prop where
  pos_w : 0 < w
  pos_N : 0 < N
  le_U : N ≤ U
  lt_pow_U : U < 2 ^ w
  le_pow_V : V ≤ 2 ^ w
  meta_le_item : metaBase + offCompItems U w N ≤ itemBase
  item_le_frontier : itemBase + compactedItemWords U V w N m_items ≤ s.frontier

theorem CompEpochEnv.meta_le_frontier {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    metaBase + offCompItems U w N ≤ s.frontier :=
  henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier)

theorem CompEpochEnv.compMetaEnv {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    CompMetaEnv w (mkCompParams U V w N) metaBase s :=
  ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.meta_le_frontier⟩

theorem CompEpochEnv.compItemEnv {U V w N metaBase itemBase m_items : ℕ} {s : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) :
    CompItemEnv w (mkCompParams U V w N) itemBase m_items s :=
  ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.item_le_frontier⟩

theorem CompEpochEnv.of_mem_eq {U V w N metaBase itemBase m_items : ℕ} {s s' : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s) (hfr : s.frontier ≤ s'.frontier) :
    CompEpochEnv U V w N metaBase itemBase m_items s' :=
  ⟨henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, henv.meta_le_item,
    henv.item_le_frontier.trans hfr⟩

/-- Establish `DenseOfPhysPre` at `g = slotOf N gm b j` for any `b < numBuckets N` and
`j < bCount N gm b` under `FixedCoupled` and `CompEpochEnv`. -/
theorem FixedCoupled.denseOfPhysPre_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    DenseOfPhysPre w ((mkCompParams U V w N, metaBase),
      slotOf N (compGmAt metaBase U w N s.mem) b j) s := by
  set gm := compGmAt metaBase U w N s.mem
  set g := slotOf N gm b j
  have hg_lt : g < N := (slotOf_lt_and_injective hslot).1 b hb j hj
  refine ⟨U, V, N, henv.pos_w, henv.pos_N, henv.le_U, henv.lt_pow_U, henv.le_pow_V, rfl,
    henv.meta_le_frontier, hg_lt, fun hb_pos => ?_⟩
  have hSN := hslot.multi_total_le hb_pos
  have htd := hcpl.tailDenseInv hb_pos
  have htail := hslot.multi_tail hb_pos
  have hM_le : gm 1 ≤ maxTailItems N := htail.ntails_eq.trans_le htail.ntails_le
  refine ⟨le_trans (Nat.le_add_right _ _) hSN, fun hg_ge => ?_⟩
  have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
  have hj_ge : ¬(j < gm (gmQIdx b) * slabSize N) := fun hj_slab => hg_ge <| by
    have hs_lt : j / slabSize N < gm (gmQIdx b) :=
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 := by
      rw [(hslot.multi_slab hb_pos).nslabs_eq]
      exact (hslot.multi_slab hb_pos).ptr_lt b hb _ hs_lt
    have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j (slabSize_pos N)
    change g < gm 0 * slabSize N
    unfold g slotOf; rw [ite_eq_right hb_ne, ite_eq_left hj_slab]
    have h1 := Nat.mul_le_mul_right (slabSize N) hp_lt
    rw [Nat.add_one_mul] at h1; omega
  have ht_lt : gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) < gm 1 := by
    rw [htail.ntails_eq]; exact htail.ptr_lt b hb _ (hslot.tailOffset_lt hb_pos hb hj hj_ge).1
  have hg_eq : g = N - 1 - gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by
    unfold g slotOf; rw [ite_eq_right hb_ne, ite_eq_right hj_ge]
  have ht_eq : N - 1 - g = gm (gmTailPtrIdx N b (j - gm (gmQIdx b) * slabSize N)) := by omega
  rw [ht_eq]
  exact ⟨lt_of_lt_of_le ht_lt hM_le, htd.td_lt _ ht_lt,
    le_trans (le_of_lt (htd.dense_lt _ ht_lt)) hSN⟩

/-- Lookup agreement at `d = denseOfPhys N gm td (slotOf N gm b j)` under `FixedCoupled`. -/
theorem FixedCoupled.quot_val_at_slotOf {metaBase itemBase U V w N m_items b j : ℕ}
    {s_fix s : Memory.State}
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hm : epochTotalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let g := slotOf N gm b j
    let d := denseOfPhys N gm td g
    d < epochTotalSlots N gm ∧
    compQuotAt itemBase U V w N m_items s.mem d =
      quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g ∧
    compValAt itemBase U V w N m_items s.mem d =
      valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem g := by
  intro gm td g d
  have htd := fun hb_pos => hcpl.tailDenseInv hb_pos
  obtain ⟨hd_lt, _, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb hj
  have hvirt := physOfDense_denseOfPhys_slotOf hslot htd hb hj
  have hq0 := hcpl.quot_eq d hd_lt
  have hv0 := hcpl.val_eq d hd_lt
  change compQuotAt itemBase U V w N (epochTotalSlots N gm) s.mem d =
    quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physOfDense N gm (compDTAt metaBase U w N s.mem) d) at hq0
  change compValAt itemBase U V w N (epochTotalSlots N gm) s.mem d =
    valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physOfDense N gm (compDTAt metaBase U w N s.mem) d) at hv0
  rw [hvirt] at hq0 hv0
  exact ⟨hd_lt,
    (compQuotAt_of_lt s.mem (lt_of_lt_of_le hd_lt hm) hd_lt).trans hq0,
    (compValAt_of_lt s.mem (lt_of_lt_of_le hd_lt hm) hd_lt).trans hv0⟩

/-- In-place value update at `slotOf N gm b j` preserves `FixedCoupled`. -/
theorem FixedCoupled.writeVal_slotOf {metaBase itemBase U V w N b j v : ℕ}
    {s_fix s : Memory.State}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hslot : SlotStoreInv N (compGmAt metaBase U w N s.mem))
    (hb : b < numBuckets N) (hj : j < bCount N (compGmAt metaBase U w N s.mem) b)
    (hv_lt : v < 2 ^ valBits V) :
    let gm := compGmAt metaBase U w N s.mem
    let td := compTDAt metaBase U w N s.mem
    let g := slotOf N gm b j
    let d := denseOfPhys N gm td g
    let s' : Memory.State :=
      { mem := writeCompVal itemBase U V w N s.mem d v, frontier := s.frontier }
    let s_fix' := (Memory.spec 0).clientState s_fix
      (writeValProg U V (ghostW w) N (epochHashSpace U (ghostW w) N) ((0, g), v))
    FixedCoupled metaBase itemBase U V w N s_fix' s' := by
  intro gm td g d s' s_fix'
  have hwg : 0 < ghostW w := by unfold ghostW; omega
  have hg_lt : g < N := (slotOf_lt_and_injective hslot).1 b hb j hj
  have htd := fun hb_pos => hcpl.tailDenseInv hb_pos
  obtain ⟨hd_lt, _, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb hj
  have hvirt := physOfDense_denseOfPhys_slotOf hslot htd hb hj
  obtain ⟨hlm_f, hgm_f, htd_f, hdt_f⟩ :=
    writeCompVal_meta_frame (metaBase := metaBase) (U := U) (V := V) (N := N) (v := v)
      hw hitem hd_lt s.mem
  obtain ⟨_, _, hq_fix, hv_fix, hl_fix, hg_fix⟩ :=
    writeValProg_effect (base := 0) (U := U) (V := V) (w := ghostW w) (n_max := N)
      (h_space := epochHashSpace U (ghostW w) N) hwg hg_lt hv_lt s_fix
  unfold FixedCoupled
  dsimp only [s', s_fix']
  refine ⟨hgm_f.trans (hg_fix.symm ▸ hcpl.gm_eq),
    hlm_f.trans (hl_fix.symm ▸ hcpl.lm_eq),
    by rw [hgm_f, htd_f, hdt_f]; exact hcpl.win_inv,
    fun i => by rw [htd_f]; exact hcpl.td_lt i,
    fun i => by rw [hdt_f]; exact hcpl.dt_lt i,
    fun d' hd' => ?_,
    fun d' hd' => ?_⟩
  · rw [hgm_f] at hd' ⊢
    rw [compQuotAt_writeCompVal hw s.mem, hdt_f, hq_fix]
    exact hcpl.quot_eq d' hd'
  · rw [hgm_f] at hd' ⊢
    rw [hdt_f, hv_fix]
    by_cases hdeq : d' = d
    · subst hdeq
      rw [compValAt_writeCompVal_self s.mem hd_lt hv_lt]
      change v = Function.update (valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        s_fix.mem) g v (physOfDense N gm (compDTAt metaBase U w N s.mem) d)
      rw [hvirt, Function.update_self]
    · rw [compValAt_writeCompVal_of_ne hw s.mem hdeq]
      have hg_ne : physByBase N (gm 0 * slabSize N) (compDTAt metaBase U w N s.mem) d' ≠ g := by
        intro heq
        apply hdeq
        obtain ⟨hb'_lt, hj'_lt, hd'_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd'
        have hv' := physOfDense_eq_slotOf_owner hslot htd hd'
        change physOfDense N gm (compDTAt metaBase U w N s.mem) d' = g at heq
        rw [hv'] at heq
        obtain ⟨rfl, rfl⟩ := (slotOf_lt_and_injective hslot).2 _ hb'_lt _ hj'_lt b hb j hj heq
        exact hd'_eq.symm
      rw [Function.update_of_ne hg_ne]
      exact hcpl.val_eq d' hd'

/-- Frame relation for operations that write exclusively to the compacted `GlobalMeta` slice
`[metaBase + offCompGM U w N, metaBase + offTailToDense U w N)`. -/
structure CompGmFrame (metaBase itemBase U V w N m_items : ℕ)
    (s s' : Memory.State) : Prop where
  frontier_eq : s'.frontier = s.frontier
  outside_eq : ∀ a, ¬(metaBase + offCompGM U w N ≤ a ∧ a < metaBase + offTailToDense U w N) →
    s'.mem a = s.mem a
  lm_eq : compLmAt metaBase U w N s'.mem = compLmAt metaBase U w N s.mem
  td_eq : compTDAt metaBase U w N s'.mem = compTDAt metaBase U w N s.mem
  dt_eq : compDTAt metaBase U w N s'.mem = compDTAt metaBase U w N s.mem
  quot_eq : compQuotAt itemBase U V w N m_items s'.mem =
    compQuotAt itemBase U V w N m_items s.mem
  val_eq : compValAt itemBase U V w N m_items s'.mem =
    compValAt itemBase U V w N m_items s.mem

theorem compGmFrame_writeCompGMGenProg {metaBase itemBase U V w N m_items idx val : ℕ}
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hidx : idx < globalMetaLen N) (hval : val < 2 ^ globalPtrBits N) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val))
    CompGmFrame metaBase itemBase U V w N m_items s s' ∧
    compGmAt metaBase U w N s'.mem = Function.update (compGmAt metaBase U w N s.mem) idx val := by
  intro s'
  have hs' := clientState_writeCompGMGenProg U V w N metaBase idx val s
  obtain ⟨hgm, hlm, htd, hdt, hq, hv, hout⟩ :=
    writeCompGM_effect (metaBase := metaBase) (itemBase := itemBase) (U := U) (V := V)
      (m_items := m_items) hw hitem hidx hval s.mem
  dsimp only [s']; rw [hs']
  exact ⟨⟨rfl, hout, hlm, htd, hdt, hq, hv⟩, hgm⟩

theorem validProg_bind_unit {β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog Unit} {q : Memory.Prog β}
    (hp : ValidProg w 0 s p)
    (hq : ∀ s' : Memory.State, s' = (Memory.spec 0).clientState s p → ValidProg w 0 s' q) :
    ValidProg w 0 s (p >>= fun _ => q) :=
  validProg_bind hp (hq _ rfl)

theorem validProg_bind_of_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {k : α → Memory.Prog β} {a : α}
    (hp : ValidProg w 0 s p)
    (hres : (Memory.spec 0).clientResult s p = a)
    (hk : ∀ s' : Memory.State, s' = (Memory.spec 0).clientState s p → ValidProg w 0 s' (k a)) :
    ValidProg w 0 s (p >>= k) := by
  refine validProg_bind hp ?_
  rw [hres]
  exact hk _ rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
