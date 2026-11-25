/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.Realize

/-!
# Backyard Prefix, Pointer Table, and Target-Permutation Specs for `csrToFastGenProg`

This internal module implements Phases A, B, and C's target evaluator of `csrToFastGenProg`:
* **`bpPrefixLoopProg`** (Phase A): computes `buildBackPrefix` into the even slots
  `offBktMeta[2 * x]` (`x ≤ M`), preserving candidate salts in odd slots `offBktMeta[16 * b + 1]`.
* **`fillBackPtrOuterLoopProg`** (Phase B): populates `offBackPtr[b * cb + k]` from `offFbStart`
  and `offBktMeta[2 * b]`.
* **`csrPermute_eval_spec`** (Phase C helper): certifies `permEvalActDestProg` at `mode = 2` for
  the in-place `permuteByTargetProg` compaction from CSR slots to front-yard/backyard locations.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bpPrefixLoopProg`,
  `fillBackPtrOuterLoopProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bpPrefixLoop`,
  `bpPrefixLoop_safe`, `bpPrefixLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fillBackPtrOuterLoop`,
  `fillBackPtrOuterLoop_safe`, `fillBackPtrOuterLoop_spec`, `csrPermute_eval_spec`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Phase A: `bpPrefixLoopProg` (`buildBackPrefix` into even slots `offBktMeta[2 * x]`) -/

/-- Single bucket step of `bpPrefixLoopProg`. -/
@[irreducible] def bpPrefixStepProg : HealRt × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (rt, (b_in, acc_in)) => do
    let b ← pure b_in
    let acc ← pure acc_in
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxOut ← pure (2 * b1)
    if lo ≤ hi then
      let xb ← pure (hi - lo)
      if hlCF rt ≤ xb then
        let exc ← pure (xb - hlCF rt)
        if acc ≤ hlNMax rt then
          let remN ← pure (hlNMax rt - acc)
          if exc ≤ remN then
            let acc1 ← pure (acc + exc)
            writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc1)
            pure (b1, acc1)
          else
            writePackedGenProg
              ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), hlNMax rt)
            pure (b1, hlNMax rt)
        else
          writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), hlNMax rt)
          pure (b1, hlNMax rt)
      else
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc)
        pure (b1, acc)
    else
      writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc)
      pure (b1, acc)

private theorem memoryCost_bpPrefixStep_pos (d : HealRt × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (bpPrefixStepProg d) s := by
  rcases d with ⟨rt, b, acc⟩
  unfold bpPrefixStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

/-- Precondition for `bpPrefixStepProg`. -/
@[expose] def BpPrefixStepPre (w : ℕ) : HealRt × (ℕ × ℕ) → Memory.State → Prop
  | (rt, (b, _acc)), _s => HealRtEnvGen w rt ∧ b < hlM rt

private theorem realizes_bpPrefixStep :
    Realizes .exact bpPrefixStepProg
      (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      BpPrefixStepPre
      (fun _ _ => 0) := by
  unfold bpPrefixStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b, acc⟩
    dsimp only [BpPrefixStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlM, hlCF, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * (b + 1)) (by omega))
  )

/-- Loop writing `buildBackPrefix` into `offBktMeta[2 * x]` across `rem` buckets. -/
@[irreducible] def bpPrefixLoopProg : (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((rt, acc), rem) => iterate bpPrefixStepProg rt rem acc

/-- `Realizes .exact` certificate for `bpPrefixLoopProg`. -/
theorem realizes_bpPrefixLoop :
    Realizes .exact bpPrefixLoopProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((rt, acc), rem) s =>
        iterationSafe bpPrefixStepProg BpPrefixStepPre w rt rem acc s)
      (fun _ _ => 0) := by
  unfold bpPrefixLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_bpPrefixStep
    memoryCost_bpPrefixStep_pos

/-- Loop-safety invariant for `bpPrefixLoopProg`. -/
theorem bpPrefixLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ acc₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe bpPrefixStepProg BpPrefixStepPre w rt rem (b₀, acc₀) s := by
  intro rt rem b₀ acc₀ s hle
  refine iterationSafe_of_stepInv _ _ _ _ (fun j p _ => p.1 + j ≤ numBucketsWhp n_max)
    (fun j p t (h : p.1 + (j + 1) ≤ _) => ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩,
      show p.1 < numBucketsWhp n_max by omega⟩, ?_⟩) hle
  show _ + j ≤ _
  obtain ⟨b, acc⟩ := p
  unfold bpPrefixStepProg
  simp only [pure_bind, clientResult_bind]
  split_ifs <;> simp only [clientResult_bind, StateTransitionSpec.clientResult_pure] <;> omega

/-- Exact memory specification of `bpPrefixLoopProg`. -/
theorem bpPrefixLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbp_le : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart
      (numBucketsWhp n_max) ≤ n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let bp := buildBackPrefix M (capFrontWhp n_max) fbStart
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ x ≤ b₀,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (2 * x) =
          bp x) →
      (∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx) →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := bpPrefixLoopProg ((rt, (b₀, bp b₀)), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ x ≤ b₀ + rem,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (2 * x) =
          bp x) ∧
      (∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M bp rem b₀ s hle hev hodd hout
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M (capFrontWhp n_max) fbStart
  unfold bpPrefixLoopProg
  obtain ⟨-, hvp, hb_eq, -, hev', hodd', hout', hfr'⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := bpPrefixStepProg) (d := rt) (n := rem)
    (safe := fun _ _ _ => True) (a := (b₀, bp b₀)) (s := s)
    (fun k p t => p.1 = b₀ + k ∧ p.2 = bp p.1 ∧
      (∀ x ≤ p.1,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem (2 * x) =
          bp x) ∧
      (∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        t.mem a = s₀.mem a) ∧
      t.frontier = s.frontier)
    (fun k hk p t ⟨hb, hacc, hev, hodd, hout, hfr⟩ => by
      obtain ⟨b, acc⟩ := p
      dsimp only at hb hacc hev
      subst hacc
      have hb_lt : b < M := by omega
      have hfb_s : ∀ x ≤ M,
          readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w t.mem x =
            fbStart x :=
        fun x hx => (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr ha1))
          (Nat.lt_succ_of_le hx)).trans (hfb_mem x hx)
      have hlo_hi := hfb_adj b hb_lt
      have hbp1_eq := hbp_adj b hb_lt
      have hbp1_le : bp (b + 1) ≤ n_max := (hbp_mono (b + 1) M hb_lt le_rfl).trans hbp_le
      have hbp0_le : bp b ≤ n_max := (hbp_mono b (b + 1) (Nat.le_succ b) hb_lt).trans hbp1_le
      have hidx_ev : 2 * (b + 1) < 16 * M := by omega
      have hbp1_pow : bp (b + 1) < 2 ^ globalPtrBits n_max :=
        lt_two_pow_globalPtrBits_of_le_n_max hbp1_le
      set m1 := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem
        (2 * (b + 1)) (bp (b + 1))
      have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) t
          (bpPrefixStepProg (rt, (b, bp b)))
          { mem := m1, frontier := t.frontier } (b + 1, bp (b + 1)) := by
        unfold bpPrefixStepProg
        dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax, hlCF, hlGBits, hlOffBm, hlOffFb]
        simp only [pure_bind]
        change bp (b + 1) = bp b + ((fbStart (b + 1) - fbStart b) - capFrontWhp n_max) at hbp1_eq
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s b hb_lt.le)).bind ?_
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s (b + 1) hb_lt)).bind ?_
        by_cases hcf : capFrontWhp n_max ≤ fbStart (b + 1) - fbStart b
        · have hexc_le : (fbStart (b + 1) - fbStart b) - capFrontWhp n_max ≤ n_max - bp b := by
            omega
          simp only [hlo_hi, hcf, hbp0_le, hexc_le, ↓reduceIte, ← hbp1_eq]
          exact (StepSpec.writePackedGen hw hgk hidx_ev hbm_b).bind (StepSpec.pure _ _)
        · have hbp1_same : bp (b + 1) = bp b := by omega
          simp only [hlo_hi, hcf, ↓reduceIte]
          dsimp only [m1]; rw [hbp1_same]
          exact (StepSpec.writePackedGen hw hgk hidx_ev hbm_b).bind (StepSpec.pure _ _)
      refine ⟨trivial, hs1.2.2, ?_⟩
      rw [hs1.1, hs1.2.1]
      refine ⟨show b + 1 = _ by omega, rfl, fun x (hx : x ≤ b + 1) => ?_,
        fun idx hidx hmod => ?_, fun a ha => ?_, hfr⟩
      · dsimp only [m1]
        rcases Nat.le_iff_lt_or_eq.mp hx with hlt | rfl
        · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hev x (Nat.le_of_lt_succ hlt)
        · exact readPacked_writePacked_self _ _ _ _ _ hbp1_pow
      · dsimp only [m1]
        rw [readPacked_writePacked_of_ne hw _ (by omega)]
        exact hodd idx hidx hmod
      · dsimp only [m1]
        rw [writePacked_outside hw _ hidx_ev _ (by omega)]; exact hout a ha)
    ⟨rfl, rfl, hev, hodd, hout, rfl⟩
  exact ⟨hfr', hvp, fun x hx => hev' x (by omega), hodd', hout'⟩

/-! ## Phase B: `fillBackPtrOuterLoopProg` (populate `offBackPtr[b * cb + k]`) -/

private def fillBackPtrInnerStepProg :
    (HealRt × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog ℕ
  | ((rt, (b_in, (remBack_in, bpb_in))), k_in) => do
    let b ← pure b_in
    let remBack ← pure remBack_in
    let bp_b ← pure bpb_in
    let k ← pure k_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let k1 ← pure (k + one_v)
    let idx ← pure (b * hlCB rt + k)
    if k < remBack then
      if bp_b ≤ hlNMax rt then
        let remN ← pure (hlNMax rt - bp_b)
        if k ≤ remN then
          let v ← pure (bp_b + k)
          writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), v)
          pure k1
        else
          writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
          pure k1
      else
        writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
        pure k1
    else
      writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
      pure k1

private theorem memoryCost_fillBackPtrInnerStep_pos
    (d : (HealRt × (ℕ × (ℕ × ℕ))) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillBackPtrInnerStepProg d) s := by
  rcases d with ⟨⟨rt, b, remBack, bp_b⟩, k⟩
  unfold fillBackPtrInnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  split_ifs <;> (rw [memoryCost_bind]; change 0 < 4 + _; omega)

private def FillBackPtrInnerPre (w : ℕ)
    (d : (HealRt × (ℕ × (ℕ × ℕ))) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.1.2.1 < hlM d.1.1 ∧ d.2 < hlCB d.1.1

private theorem realizes_fillBackPtrInnerStep :
    Realizes .exact fillBackPtrInnerStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillBackPtrInnerPre
      (fun _ _ => 0) := by
  unfold fillBackPtrInnerStepProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, b, remBack, bp_b⟩, k⟩
    dsimp only [FillBackPtrInnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt, hk_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlM, hlCB, hlGBits, hlOffBp] at *
    have hidx := mul_add_lt_mul_bound hb_lt hk_lt
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hidx hseg
  )

@[irreducible] private def fillBackPtrInnerLoopProg :
    ((HealRt × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, k₀), rem) => iterate fillBackPtrInnerStepProg cfg rem k₀

private theorem realizes_fillBackPtrInnerLoop :
    Realizes .exact fillBackPtrInnerLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, k₀), rem) s =>
        iterationSafe fillBackPtrInnerStepProg FillBackPtrInnerPre w cfg rem k₀ s)
      (fun _ _ => 0) := by
  unfold fillBackPtrInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ))
    realizes_fillBackPtrInnerStep
    memoryCost_fillBackPtrInnerStep_pos

private theorem fillBackPtrInnerLoop_safe {c U V w n_max base b remBack bp_b : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ capBackWhp n_max →
      iterationSafe fillBackPtrInnerStepProg FillBackPtrInnerPre w
        (rt, (b, (remBack, bp_b))) rem k₀ s :=
  iterationSafe_of_stateless_step fillBackPtrInnerStepProg FillBackPtrInnerPre
    (fun _ hk _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb, hk⟩)
    (fun _ _ _ => by
      unfold fillBackPtrInnerStepProg; dsimp only [writePackedGenProg]
      simp only [pure_bind]; split_ifs <;> (rw [clientResult_bind]; rfl))

private theorem fillBackPtrInnerLoop_spec {c U V w n_max base b remBack bp_b : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hsum_le : bp_b + remBack ≤ n_max) (s : Memory.State) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cb := capBackWhp n_max
    let prog := fillBackPtrInnerLoopProg (((rt, (b, (remBack, bp_b))), 0), cb)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ k < cb,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
        (b * cb + k) = if k < remBack then bp_b + k else 0) ∧
    (∀ b' < M, b' ≠ b → ∀ k < cb,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
        (b' * cb + k) =
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
          (b' * cb + k)) ∧
    (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
      s'.mem a = s.mem a) := by
  intro rt M cb
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  have hbp_b_seg : base + offBackPtr c U V w n_max +
      packedWords (M * cb) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hbp_end : offBackPtr c U V w n_max +
      packedWords (M * cb) (globalPtrBits n_max) w = offBackAux c U V w n_max := rfl
  unfold fillBackPtrInnerLoopProg
  obtain ⟨-, hvp, -, hprev, hoth, hout, hfr⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := fillBackPtrInnerStepProg)
    (d := (rt, (b, (remBack, bp_b)))) (n := cb) (safe := fun _ _ _ => True) (a := 0) (s := s)
    (fun k k' t => k' = k ∧
      (∀ j < k, readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w t.mem
        (b * cb + j) = if j < remBack then bp_b + j else 0) ∧
      (∀ b' < M, b' ≠ b → ∀ j < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w t.mem
          (b' * cb + j) =
          readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
            (b' * cb + j)) ∧
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        t.mem a = s.mem a) ∧
      t.frontier = s.frontier)
    (fun k hk k' t ⟨hk', hprev, hoth, hout, hfr⟩ => by
      subst k'
      have hidx := mul_add_lt_mul_bound hb hk
      set vVal := if k < remBack then bp_b + k else 0
      have hv_pow : vVal < 2 ^ globalPtrBits n_max := by
        dsimp only [vVal]; split_ifs <;> exact lt_two_pow_globalPtrBits_of_le_n_max (by omega)
      set m1 := writePacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w t.mem
        (b * cb + k) vVal
      have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) t
          (fillBackPtrInnerStepProg ((rt, (b, (remBack, bp_b))), k))
          { mem := m1, frontier := t.frontier } (k + 1) := by
        unfold fillBackPtrInnerStepProg
        dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax, hlCB, hlGBits, hlOffBp]
        simp only [pure_bind]
        by_cases hkr : k < remBack
        · have h1 : bp_b ≤ n_max := by omega
          have h2 : k ≤ n_max - bp_b := by omega
          simp only [hkr, h1, h2, ↓reduceIte]
          dsimp only [m1, vVal]; simp only [hkr, ↓reduceIte]
          exact (StepSpec.writePackedGen hw hgk hidx hbp_b_seg).bind (StepSpec.pure _ _)
        · simp only [hkr, ↓reduceIte]
          dsimp only [m1, vVal]; simp only [hkr, ↓reduceIte]
          exact (StepSpec.writePackedGen hw hgk hidx hbp_b_seg).bind (StepSpec.pure _ _)
      refine ⟨trivial, hs1.2.2, ?_⟩
      rw [hs1.1, hs1.2.1]
      refine ⟨rfl, fun j hj => ?_, fun b' hb' hne j hj => ?_, fun a ha => ?_, hfr⟩
      · dsimp only [m1]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev j hlt
        · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
      · rw [← hoth b' hb' hne j hj]
        have hne_idx : b' * cb + j ≠ b * cb + k := by
          intro heq
          have hcb_pos : 0 < cb := by omega
          have hd1 : (b' * cb + j) / cb = b' := by
            rw [mul_comm, Nat.mul_add_div hcb_pos, Nat.div_eq_of_lt hj, Nat.add_zero]
          have hd2 : (b * cb + k) / cb = b := by
            rw [mul_comm, Nat.mul_add_div hcb_pos, Nat.div_eq_of_lt hk, Nat.add_zero]
          exact hne (by rw [← hd1, heq, hd2])
        exact readPacked_writePacked_of_ne hw _ hne_idx _
      · rw [← hout a ha]
        dsimp only [M, cb] at hidx hbp_end
        exact writePacked_outside hw _ hidx _ (by omega))
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩
  exact ⟨hfr, hvp, hprev, hoth, hout⟩

/-- Single bucket step of `fillBackPtrOuterLoopProg`. -/
@[irreducible] def fillBackPtrOuterStepProg : HealRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxBm ← pure (2 * b)
    let bp_b ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxBm)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      if hlCF rt ≤ cnt then
        let remBack ← pure (cnt - hlCF rt)
        let _ ← fillBackPtrInnerLoopProg (((rt, (b, (remBack, bp_b))), zero_v), hlCB rt)
        pure b1
      else
        let _ ← fillBackPtrInnerLoopProg (((rt, (b, (zero_v, bp_b))), zero_v), hlCB rt)
        pure b1
    else
      let _ ← fillBackPtrInnerLoopProg (((rt, (b, (zero_v, bp_b))), zero_v), hlCB rt)
      pure b1

private theorem memoryCost_fillBackPtrOuterStep_pos (d : HealRt × ℕ) (s : Memory.State) :
    0 < memoryCost (fillBackPtrOuterStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold fillBackPtrOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private theorem realizes_fillBackPtrOuterStep :
    Realizes .exact fillBackPtrOuterStepProg
      (WordEncoding.encode (α := HealRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      HealBktStepPre
      (fun _ _ => 0) := by
  unfold fillBackPtrOuterStepProg
  have hrp := realizes_readPackedGen
  have hil := realizes_fillBackPtrInnerLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [HealBktStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * b) (by omega))
    | exact fillBackPtrInnerLoop_safe henv hb_lt (capBackWhp n_max) 0 s (by omega)
  )

/-- Outer bucket loop populating `offBackPtr`. -/
@[irreducible] def fillBackPtrOuterLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillBackPtrOuterStepProg rt rem b₀

/-- `Realizes .exact` certificate for `fillBackPtrOuterLoopProg`. -/
theorem realizes_fillBackPtrOuterLoop :
    Realizes .exact fillBackPtrOuterLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillBackPtrOuterStepProg HealBktStepPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillBackPtrOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillBackPtrOuterStep
    memoryCost_fillBackPtrOuterStep_pos

/-- Loop-safety invariant for `fillBackPtrOuterLoopProg`. -/
theorem fillBackPtrOuterLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillBackPtrOuterStepProg HealBktStepPre w rt rem b₀ s :=
  iterationSafe_of_stateless_step fillBackPtrOuterStepProg HealBktStepPre
    (fun _ hb _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb⟩)
    (fun _ _ _ => by
      unfold fillBackPtrOuterStepProg; dsimp only [readPackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs <;> (rw [clientResult_bind]; rfl))

/-- Exact memory specification of `fillBackPtrOuterLoopProg`. -/
theorem fillBackPtrOuterLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbp_le : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart
      (numBucketsWhp n_max) ≤ n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x)
    (hbp_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem (2 * x) =
        buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf fbStart
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ b < b₀, ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
          (b * cb + k) = if k < (fbStart (b + 1) - fbStart b) - cf then bp b + k else 0) →
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillBackPtrOuterLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem, ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
          (b * cb + k) = if k < (fbStart (b + 1) - fbStart b) - cf then bp b + k else 0) ∧
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M cf cb bp rem b₀ s hle hprev hout
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hfb_end : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w = offBackPtr c U V w n_max := rfl
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M cf fbStart
  unfold fillBackPtrOuterLoopProg
  obtain ⟨-, hvp, hb_eq, hprev', hout', hfr'⟩ := validProg_iterate_of_inv (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (body := fillBackPtrOuterStepProg) (d := rt)
    (n := rem) (safe := fun _ _ _ => True) (a := b₀) (s := s)
    (fun k b t => b = b₀ + k ∧
      (∀ b' < b, ∀ j < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w t.mem
          (b' * cb + j) = if j < (fbStart (b' + 1) - fbStart b') - cf then bp b' + j else 0) ∧
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        t.mem a = s₀.mem a) ∧
      t.frontier = s.frontier)
    (fun k hk b t ⟨hb, hprev, hout, hfr⟩ => by
      have hb_lt : b < M := by omega
      have hfb_s : ∀ x ≤ M,
          readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w t.mem x =
            fbStart x :=
        fun x hx => (readPacked_congr hw (hidx := show x < M + 1 by omega)
          (fun a ⟨_, ha2⟩ => hout a (Or.inl (by dsimp only [M] at hfb_end ha2; omega)))).trans
          (hfb_mem x hx)
      have hbp_s : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w t.mem
          (2 * b) = bp b :=
        (readPacked_congr hw (hidx := show 2 * b < 16 * M by omega)
          (fun a ⟨_, ha2⟩ =>
            hout a (Or.inl (by dsimp only [M] at hbm_end hfb_end ha2; omega)))).trans
          (hbp_mem b hb_lt.le)
      have hlo_hi := hfb_adj b hb_lt
      set remBack := (fbStart (b + 1) - fbStart b) - cf
      have hsum_le : bp b + remBack ≤ n_max := by
        have h1 : bp (b + 1) = bp b + remBack := hbp_adj b hb_lt
        have h2 : bp (b + 1) ≤ n_max := (hbp_mono (b + 1) M hb_lt le_rfl).trans hbp_le
        omega
      obtain ⟨hin_f, hin_vp, hin_k, hin_oth, hin_out⟩ := fillBackPtrInnerLoop_spec
        (b := b) (remBack := remBack) (bp_b := bp b) henv hb_lt hsum_le t
      set inProg := fillBackPtrInnerLoopProg (((rt, (b, (remBack, bp b))), 0), cb)
      set s_in := (Memory.spec 0).clientState t inProg
      have hin_step : StepSpec w (base + largeSpaceWhp c U V w n_max) t inProg s_in
          ((Memory.spec 0).clientResult t inProg) := ⟨rfl, rfl, hin_vp⟩
      set p1 := fillBackPtrOuterStepProg (rt, b)
      have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) t p1 s_in (b + 1) := by
        dsimp only [p1]; unfold fillBackPtrOuterStepProg
        dsimp only [rt, mkHealRt, hlBase, hlW, hlCF, hlCB, hlGBits, hlOffBm, hlOffFb] at hin_step ⊢
        simp only [pure_bind]
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s b hb_lt.le)).bind ?_
        refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s (b + 1) hb_lt)).bind ?_
        refine (StepSpec.readPackedGen_eq hw (by omega) hbm_b hbp_s).bind ?_
        by_cases hcf : cf ≤ fbStart (b + 1) - fbStart b
        · simp only [hlo_hi, show capFrontWhp n_max ≤ fbStart (b + 1) - fbStart b from hcf,
            ↓reduceIte]
          exact hin_step.bind (StepSpec.pure _ _)
        · have hrem0 : remBack = 0 := by dsimp only [remBack]; omega
          simp only [hlo_hi, show ¬(capFrontWhp n_max ≤ fbStart (b + 1) - fbStart b) from hcf,
            ↓reduceIte]
          dsimp only [inProg] at hin_step
          rw [hrem0] at hin_step
          exact hin_step.bind (StepSpec.pure _ _)
      refine ⟨trivial, hs1.2.2, ?_⟩
      rw [hs1.1, hs1.2.1]
      refine ⟨by omega, fun b' hb' j hj => ?_, fun a ha => (hin_out a ha).trans (hout a ha),
        hin_f.trans hfr⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb' with hlt | rfl
      · rw [hin_oth b' (hlt.trans hb_lt) (by omega) j hj]; exact hprev b' hlt j hj
      · exact hin_k j hj)
    ⟨rfl, hprev, hout, rfl⟩
  exact ⟨hfr', hvp, fun b' hb' => hprev' b' (by omega), hout'⟩

/-! ## Phase C Target-Evaluator Specification (`permEvalActDestProg` at `mode = 2`) -/

/-- Exact target-slot specification of `permEvalActDestProg` at `mode = 2` for `csrToFast`. -/
theorem csrPermute_eval_spec {c U V w n_max base : ℕ} {csr : CsrState}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb0 : csr.fbStart 0 = 0)
    (hfb_adj : ∀ b < numBucketsWhp n_max, csr.fbStart b ≤ csr.fbStart (b + 1))
    (hback_cb : ∀ b < numBucketsWhp n_max,
      (csr.fbStart (b + 1) - csr.fbStart b) - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
      (numBucketsWhp n_max) ≤ poolSizeWhp n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = csr.fbStart x)
    (hbp_mem : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) =
        if k < (csr.fbStart (b + 1) - csr.fbStart b) - capFrontWhp n_max then
          buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart b + k
        else 0) :
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let bp := buildBackPrefix M cf csr.fbStart
    let bktCnt : ℕ → ℕ := fun b => if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0
    let backPtr : ℕ → ℕ → ℕ := fun b k =>
      if b < M ∧ k < bktCnt b - cf then bp b + k else 0
    let act₀ : ℕ → Bool := fun i => decide (i < csr.fbStart M)
    let dest : ℕ → ℕ := fun i =>
      let b := csrBucketOfIdx csr.fbStart i M
      let loc := i - csr.fbStart b
      if loc < cf then b * cf + loc
      else M * cf + backPtr b (loc - cf)
    ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x))).1 =
          (if act₀ x then 1 else 0) ∧
      (act₀ x = true →
        ((Memory.spec 0).clientResult s'
          (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x))).2 = dest x ∧
        dest x < n_max) := by
  intro M cf bp bktCnt backPtr act₀ dest x _ s' hout
  have hw := henv.2.1
  have hMcf_le : M * cf ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  have hls_fb : offLocState c U V w n_max ≤ offFbStart c U V w n_max := by
    unfold offFbStart offBktMeta; omega
  have hls_bp : offLocState c U V w n_max ≤ offBackPtr c U V w n_max := by
    unfold offBackPtr offFbStart offBktMeta; omega
  have hfb_s' : ∀ z ≤ M,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s'.mem z =
        csr.fbStart z := fun z hz =>
    (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
      (Nat.lt_succ_of_le hz)).trans (hfb_mem z hz)
  have hbp_s' : ∀ b < M, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
        (b * capBackWhp n_max + k) = backPtr b k := by
    intro b hb k hk
    rw [readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
      (mul_add_lt_mul_bound hb hk), hbp_mem b hb k hk]
    dsimp only [backPtr, bktCnt]
    by_cases hk' : k < (csr.fbStart (b + 1) - csr.fbStart b) - cf
    · rw [ite_eq_left hk', ite_eq_left ⟨hb, by simp only [hb, ↓reduceIte]; exact hk'⟩]
    · have hnot : ¬(b < M ∧ k < (if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0) - cf) :=
        fun h => hk' (by have h2 := h.2; simp only [hb, ↓reduceIte] at h2; exact h2)
      rw [ite_eq_right hk', ite_eq_right hnot]
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M cf csr.fbStart
  let fbRd := fun k => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
    s'.mem k
  let b_rd := csrBucketOfIdx fbRd x (numBucketsWhp n_max)
  have hfbM : fbRd (numBucketsWhp n_max) = csr.fbStart M := hfb_s' M le_rfl
  have hb_congr : b_rd = csrBucketOfIdx csr.fbStart x M := csrBucketOfIdx_congr hfb_s'
  have hboth :
      (Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x)) =
        (if act₀ x then (1, dest x) else (0, 0)) ∧
      (act₀ x = true → dest x < n_max) := by
    rw [clientResult_permEvalActDestProg_of_ne_one henv (by decide) s']
    change (if x < fbRd (numBucketsWhp n_max) then
        if b_rd < numBucketsWhp n_max then
          if x < fbRd b_rd then (0, 0)
          else if x - fbRd b_rd < capFrontWhp n_max then
            (1, b_rd * capFrontWhp n_max + (x - fbRd b_rd))
          else if x - fbRd b_rd - capFrontWhp n_max < capBackWhp n_max then
            if readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
                (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) <
                poolSizeWhp n_max then
              (1, numBucketsWhp n_max * capFrontWhp n_max +
                readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
                  (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)))
            else (0, 0)
          else (0, 0)
        else (0, 0)
      else (0, 0)) = (if act₀ x then (1, dest x) else (0, 0)) ∧ _
    by_cases hxN : x < csr.fbStart M
    · have hxN_rd : x < fbRd (numBucketsWhp n_max) := hfbM.symm ▸ hxN
      set b_x := csrBucketOfIdx csr.fbStart x M
      obtain ⟨hb_x, hlo_x, hhi_x⟩ := csrBucketOfIdx_spec hfb0 hfb_adj M le_rfl x hxN
      have hb_x' : b_x < M := hb_x
      have hlo_x' : csr.fbStart b_x ≤ x := hlo_x
      have hhi_x' : x < csr.fbStart (b_x + 1) := hhi_x
      have hb_x_rd : b_rd < numBucketsWhp n_max := hb_congr.symm ▸ hb_x'
      have hfb_bx : fbRd b_rd = csr.fbStart b_x := by
        dsimp only [fbRd]; rw [hb_congr]; exact hfb_s' b_x hb_x'.le
      have hnot_lt_rd : ¬(x < fbRd b_rd) := by rw [hfb_bx]; exact Nat.not_lt.mpr hlo_x'
      have ha_true : act₀ x = true := by dsimp only [act₀]; exact decide_eq_true hxN
      rw [ite_eq_left hxN_rd, ite_eq_left hb_x_rd, ite_eq_right hnot_lt_rd, ha_true,
        ite_eq_left rfl]
      set loc_x := x - csr.fbStart b_x
      by_cases hcf : loc_x < cf
      · have hcf_rd : x - fbRd b_rd < capFrontWhp n_max := by rw [hfb_bx]; exact hcf
        have hd_eq : dest x = b_x * cf + loc_x := by dsimp only [dest]; exact ite_eq_left hcf
        rw [ite_eq_left hcf_rd, hfb_bx, hb_congr, hd_eq]
        exact ⟨rfl, fun _ => (mul_add_lt_mul_bound hb_x' hcf).trans_le hMcf_le⟩
      · have hcf_rd : ¬(x - fbRd b_rd < capFrontWhp n_max) := by rw [hfb_bx]; exact hcf
        set k_x := loc_x - cf
        have hk_rem : k_x < (csr.fbStart (b_x + 1) - csr.fbStart b_x) - cf := by
          dsimp only [k_x, loc_x] at hcf ⊢; omega
        have hk_cb : k_x < capBackWhp n_max := hk_rem.trans (hback_cb b_x hb_x')
        have hk_cb_rd : x - fbRd b_rd - capFrontWhp n_max < capBackWhp n_max := by
          rw [hfb_bx]; exact hk_cb
        have hbp_val_eq : backPtr b_x k_x = bp b_x + k_x := by
          dsimp only [backPtr, bktCnt]
          exact ite_eq_left ⟨hb_x', by rw [ite_eq_left hb_x']; exact hk_rem⟩
        have hbp_lt_ps : backPtr b_x k_x < poolSizeWhp n_max := by
          rw [hbp_val_eq]
          have hstep : bp (b_x + 1) = bp b_x + ((csr.fbStart (b_x + 1) - csr.fbStart b_x) - cf) :=
            hbp_adj b_x hb_x'
          have hleM : bp (b_x + 1) ≤ bp M := hbp_mono (b_x + 1) M hb_x' le_rfl
          have hbp_ps' : bp M ≤ poolSizeWhp n_max := hbp_ps
          dsimp only [k_x, loc_x] at hk_rem ⊢
          omega
        have hbp_rd : readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
            (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) = backPtr b_x k_x := by
          rw [hfb_bx, hb_congr]; exact hbp_s' b_x hb_x' k_x hk_cb
        have hbp_lt_rd : readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w
            s'.mem (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) <
            poolSizeWhp n_max := by
          rw [hbp_rd]; exact hbp_lt_ps
        have hd_lt : M * cf + backPtr b_x k_x < n_max := by
          unfold poolSizeWhp at hbp_lt_ps; dsimp only [M, cf]; omega
        have hd_eq : dest x = M * cf + backPtr b_x k_x := by
          dsimp only [dest]; exact ite_eq_right hcf
        rw [ite_eq_right hcf_rd, ite_eq_left hk_cb_rd, ite_eq_left hbp_lt_rd, hbp_rd, hd_eq]
        exact ⟨rfl, fun _ => hd_lt⟩
    · have hxN_rd : ¬(x < fbRd (numBucketsWhp n_max)) := by rw [hfbM]; exact hxN
      have ha_false : act₀ x = false := by dsimp only [act₀]; exact decide_eq_false hxN
      rw [ite_eq_right hxN_rd, ha_false, ite_eq_right Bool.false_ne_true]
      exact ⟨rfl, fun h => Bool.noConfusion h⟩
  rw [hboth.1]
  cases ha : act₀ x
  · rw [ite_eq_right Bool.false_ne_true]
    exact ⟨rfl, fun h => Bool.noConfusion h⟩
  · rw [ite_eq_left rfl]
    exact ⟨rfl, fun _ => ⟨rfl, hboth.2 ha⟩⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
