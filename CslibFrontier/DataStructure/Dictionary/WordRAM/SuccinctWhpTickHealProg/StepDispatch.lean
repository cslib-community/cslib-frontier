/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSeedCheckProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.SelfHeal
import CslibFrontier.Tactic.Realize

/-!
# Top-Level `whpStepPureGenProg` Mode Dispatcher and `O_c(1)` Fast-Branch Certificate

This module implements the top-level parameter-free `Memory.Prog` step dispatcher
`whpStepPureGenProg` across `.small`, `.fast` (both `O_c(1)` fast-branch hits and fallback
transitions via `fastToCsrGenProg` + `trySelfHealGenProg`), and `.fallback`, refining
`whpStepPure c U n_max θ st op` inside `whpSpace c U V w n_max` words with
`memoryCost ≤ whpFastBranchCost c` whenever `IsFastStepHit c U n_max ops_prev op θ` holds.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.whpFastBranchCost`, `whpStepPureGenProg`,
  `WhpStepPurePre`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_whpStepPureGen`,
  `whpStepPureGenProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-- `c`-only `memoryCost` upper bound on `whpStepPureGenProg` whenever `IsFastStepHit` holds
(`1` mode-word read plus `smallOpCostWhp c` or `fastOpCostWhp c`). -/
@[expose] def whpFastBranchCost (c : ℕ) : ℕ :=
  max (smallOpCostWhp c + 1) (fastOpCostWhp c + 1)

@[irreducible] private def fallbackAndHealGenProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp_base, opTag), uv) => do
    let res ← csrStepOpGenProg ((wp_base, opTag), uv)
    trySelfHealGenProg wp_base
    pure res

private def FallbackAndHealPre (w : ℕ)
    (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) (dict : Dictionary.State U)
      (op : Dynamic.Op U),
    WhpLargeEnv c U V w₀ n_max w d.1.1.2 ∧
    d.1.1.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.1.1.2 c U w₀ n_max θ s.mem ∧
    CsrMemRep d.1.1.2 c U V w₀ n_max csr s.mem ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) ∧
    Dynamic.valid V n_max dict op ∧
    encodeOpWhp op = (d.1.2, d.2)

private theorem realizes_fallbackAndHealGen :
    Realizes .exact fallbackAndHealGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      FallbackAndHealPre
      (fun _ _ => 0) := by
  unfold fallbackAndHealGenProg
  have hcs := realizes_csrStepOpGen
  have hsh := realizes_trySelfHealGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, opTag⟩, uv⟩
    dsimp only [FallbackAndHealPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, csr, dict, op, henv, rfl, hseed, hrep, hcsr, hqv,
      hval_op, hop_enc⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hnU := henv.2.2.2.2.1
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | (have hop1 : (encodeOpWhp op).1 = opTag := congrArg Prod.fst hop_enc
       have hop2 : (encodeOpWhp op).2 = uv := congrArg Prod.snd hop_enc
       obtain ⟨hseed1, hrep1, _, _, _, _⟩ :=
         csrStepOpGenProg_spec henv hseed hrep hcsr op hval_op (s := s)
       obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr hqv hval_op
       rw [← hop1, ← hop2]
       exact ⟨c, U, V, w, n_max, θ, (csrStepOp c U n_max θ.1 csr op).1,
         (Dynamic.step dict op).1, henv, rfl, hseed1, hrep1, hcsr1, hqv1⟩)
  )

private theorem fallbackAndHealGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := fallbackAndHealGenProg (((mkWhpParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := csrStepOp c U n_max θ.1 csr op
    WhpMemRep base c U V w n_max θ (trySelfHeal c U n_max θ pureOut.1) s'.mem ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hnU := henv.2.2.2.2.1
  obtain ⟨hseed1, hrep1, hfr1, hres1, hvp1, hout1⟩ :=
    csrStepOpGenProg_spec henv hseed hrep hcsr op hval_op (s := s)
  obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr hqv hval_op
  set s1 := (Memory.spec 0).clientState s
    (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1),
      (encodeOpWhp op).2))
  obtain ⟨hsh_rep, hsh_fr, hsh_vp, hsh_out⟩ :=
    trySelfHealGenProg_spec henv hseed1 hrep1 hcsr1 hqv1 (s := s1)
  have hstep : StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (fallbackAndHealGenProg
        (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1), (encodeOpWhp op).2))
      ((Memory.spec 0).clientState s1 (trySelfHealGenProg (mkWhpParams c U V w n_max, base)))
      (encodeOptRes (csrStepOp c U n_max θ.1 csr op).2) := by
    unfold fallbackAndHealGenProg
    exact StepSpec.bind ⟨rfl, hres1, hvp1⟩ (StepSpec.bind ⟨rfl, rfl, hsh_vp⟩ (StepSpec.pure _ _))
  dsimp only
  rw [hstep.1, hstep.2.1]
  exact ⟨hsh_rep, rfl, hsh_fr.trans hfr1, hstep.2.2, fun a ha => (hsh_out a ha).trans (hout1 a ha)⟩

/-- Top-level parameter-free `Memory.Prog` step dispatcher for `whpStepPure c U n_max θ st op`
across `.small`, `.fast`, and `.fallback` modes (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[irreducible] def whpStepPureGenProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((wp, base_in), opTag_in), uv_in) => do
    let base ← pure base_in
    let opTag ← pure opTag_in
    let uv ← pure uv_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let mode ← Memory.read base
    if mode = zero_v then
      smallStepOpGenProg (((wp.1, base), opTag), uv)
    else if mode = one_v then
      let out ← fastStepPureGenProg ((wp, base), (opTag, uv))
      if out.1 = one_v then
        pure out.2
      else
        fastToCsrGenProg (wp.1, base)
        fallbackAndHealGenProg (((wp, base), opTag), uv)
    else
      fallbackAndHealGenProg (((wp, base), opTag), uv)

/-- Precondition for `whpStepPureGenProg` (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[expose] def WhpStepPurePre (w : ℕ)
    (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let (p1, uv) := d
  let (p0, opTag) := p1
  let (wp, base) := p0
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (st : WhpDictState) (dict : Dictionary.State U)
      (op : Dynamic.Op U),
    0 < c ∧ 0 < w ∧ w = w₀ ∧ n_max ≤ U ∧ Fits w U ∧ Fits w V ∧
    Fits w (base + whpSpace c U V w₀ n_max) ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    WhpMemRep base c U V w₀ n_max θ st s.mem ∧
    ValidWhpState c U V n_max θ st dict ∧
    Dynamic.valid V n_max dict op ∧
    encodeOpWhp op = (opTag, uv)

/-- `Realizes .exact` certificate for `whpStepPureGenProg`. -/
theorem realizes_whpStepPureGen :
    Realizes .exact whpStepPureGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      WhpStepPurePre
      (fun _ _ => 0) := by
  unfold whpStepPureGenProg
  have hsm := realizes_smallStepOpGen
  have hfs := realizes_fastStepPureGen
  have hfc := realizes_fastToCsrGen
  have hfh := realizes_fallbackAndHealGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, opTag⟩, uv⟩
    dsimp only [WhpStepPurePre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, st, dict, op,
      hc_pos, hw, hw_eq, hnU, hU, hV, hfit_sp, rfl, hrep, hv, hval_op, hop_enc⟩ := h
    subst hw_eq
    simp only [hcs_r] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | (cases st with
       | small sm =>
         obtain ⟨hsm_lt, hsm_rep⟩ := hrep
         have hm0 : s.mem base = 0 := by simpa only [hdrMode, Nat.add_zero] using hsm_rep.1
         have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
           unfold mkWhpParams; exact congrArg Prod.fst (ite_eq_left hsm_lt)
         have henv_sm : WhpSmallEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hsm_lt, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | (rw [hwp1]; exact ⟨c, U, V, w, n_max, henv_sm, rfl⟩)
       | fast fs =>
         obtain ⟨hth, hseed, hfs_rep⟩ := hrep
         have hm1 : s.mem base = 1 := by simpa only [hdrMode, Nat.add_zero] using hfs_rep.2.1
         have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
           unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
         have henv_lg : WhpLargeEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, op, henv_lg, rfl, hseed, hfs_rep, hv,
             hval_op, hop_enc⟩
         | (rw [hwp1]; exact ⟨c, U, V, w, n_max, henv_lg, rfl⟩)
         | (obtain ⟨_, _, hfs_m⟩ := fastStepPureGenProg_spec henv_lg hseed hfs_rep hv hval_op
              (s := s)
            cases hfsp : fastStepPure c U n_max θ fs op with
            | some p =>
              rw [hfsp, hop_enc] at hfs_m
              exact False.elim (‹_ ≠ 1› (congrArg Prod.fst hfs_m.1))
            | none =>
              rw [hfsp, hop_enc] at hfs_m
              rw [hfs_m.2, Prod.mk.eta, hwp1]
              obtain ⟨hseed_fc, hrep_fc, _, _, _⟩ := fastToCsrGenProg_spec henv_lg hseed hfs_rep
                hv (s := s)
              obtain ⟨hcsr_fc, hqv_fc⟩ := hv.fastToCsr_spec
              exact ⟨c, U, V, w, n_max, θ, fastToCsr n_max fs, dict, op, henv_lg, rfl,
                hseed_fc, hrep_fc, hcsr_fc, hqv_fc, hval_op, hop_enc⟩)
       | fallback csr =>
         obtain ⟨hth, hseed, hcsr_rep⟩ := hrep
         obtain ⟨_, hcsr, hqv⟩ := hv
         have hm2 : s.mem base = 2 := by simpa only [hdrMode, Nat.add_zero] using hcsr_rep.1
         have henv_lg : WhpLargeEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, csr, dict, op, henv_lg, rfl, hseed, hcsr_rep, hcsr, hqv,
             hval_op, hop_enc⟩)
  )

/-- Master `Memory.Prog` refinement and conditional `O_c(1)` `memoryCost` specification for
`whpStepPureGenProg`:
* For **every** seed `θ` and valid state `(st, dict)`, refines `whpStepPure c U n_max θ st op`,
  preserves `WhpMemRep` and `frontier`, satisfies `ValidProg` inside
  `[base, base + whpSpace c U V w n_max)`, and leaves caller memory outside
  `[base, base + whpSpace c U V w n_max)` untouched;
* Whenever `st = whpRunPure c U n_max θ ops_prev` and `IsFastStepHit c U n_max ops_prev op θ`
  holds, executes in at most `whpFastBranchCost c` (`O_c(1)`) worst-case memory operations. -/
theorem whpStepPureGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {st : WhpDictState} {dict : Dictionary.State U}
    {s : Memory.State}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit_sp : Fits w (base + whpSpace c U V w n_max))
    (hrep : WhpMemRep base c U V w n_max θ st s.mem)
    (hv : ValidWhpState c U V n_max θ st dict)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := whpStepPureGenProg (((mkWhpParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := whpStepPure c U n_max θ st op
    WhpMemRep base c U V w n_max θ pureOut.1 s'.mem ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + whpSpace c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + whpSpace c U V w n_max ≤ a) → s'.mem a = s.mem a) ∧
    (∀ ops_prev : List (Dynamic.Op U),
      st = whpRunPure c U n_max θ ops_prev →
      IsFastStepHit c U n_max ops_prev op θ →
      memoryCost prog s ≤ whpFastBranchCost c) := by
  have hcs_r : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
  have hcr_r : (Memory.spec 0).clientResult s (Memory.read base) = s.mem base := rfl
  have hmc_r : memoryCost (Memory.read base) s = 1 := rfl
  have hbase_lt : base < base + whpSpace c U V w n_max := by
    have h32 : 32 ≤ whpSpace c U V w n_max := by
      unfold whpSpace; split_ifs <;> [dsimp [smallSpaceWhp]; dsimp [largeSpaceWhp]] <;> omega
    omega
  set prog := whpStepPureGenProg
    (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1), (encodeOpWhp op).2)
  dsimp only [whpFastBranchCost]
  cases st with
  | small sm =>
    obtain ⟨hsm_lt, hsm_rep⟩ := hrep
    have hsp_eq : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := ite_eq_left hsm_lt
    have hm0 : s.mem base = 0 := by simpa only [hdrMode, Nat.add_zero] using hsm_rep.1
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; exact congrArg Prod.fst (ite_eq_left hsm_lt)
    have henv_sm : WhpSmallEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hsm_lt, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hsm_out_rep, hsm_fr, hsm_res, hsm_mc, hsm_vp, hsm_out⟩ :=
      smallStepOpGenProg_spec henv_sm hsm_rep hv.2 op hval_op (s := s)
    set p_sm := match op with
      | .query u => (sm, smallQuery n_max sm u.val)
      | .delete u => (smallDelete n_max sm u.val, none)
      | .insert u v => (smallInsert n_max sm u.val v, none)
    have hwhp_eq : whpStepPure c U n_max θ (.small sm) op = (.small p_sm.1, p_sm.2) := by
      cases op <;> rfl
    rw [hwhp_eq]
    have hstep : StepSpec w (base + whpSpace c U V w n_max) s prog
        ((Memory.spec 0).clientState s
          (smallStepOpGenProg
            (((mkWhpCoreParams c U V w n_max, base), (encodeOpWhp op).1), (encodeOpWhp op).2)))
        (encodeOptRes p_sm.2) := by
      simp only [prog, whpStepPureGenProg, pure_bind, hwp1]
      refine (StepSpec.read hbase_lt).bind ?_
      simp only [hm0, ↓reduceIte, hsp_eq]
      exact ⟨rfl, hsm_res, hsm_vp⟩
    rw [hstep.1]
    refine ⟨⟨hsm_lt, hsm_out_rep⟩, hstep.2.1, hsm_fr, hstep.2.2,
      fun a ha => hsm_out a (hsp_eq ▸ ha), fun _ _ _ => ?_⟩
    unfold whpStepPureGenProg
    simp only [pure_bind, hwp1, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hmc_r, hcs_r,
      hcr_r, hm0, ↓reduceIte, Nat.add_comm 1]
    exact (Nat.add_le_add_right hsm_mc 1).trans (le_max_left _ _)
  | fast fs =>
    obtain ⟨hth, hseed, hfs_rep⟩ := hrep
    have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := ite_eq_right hth.not_gt
    have hm1 : s.mem base = 1 := by simpa only [hdrMode, Nat.add_zero] using hfs_rep.2.1
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
    have henv_lg : WhpLargeEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hfs_mc, hfs_vp, hfs_m⟩ :=
      fastStepPureGenProg_spec henv_lg hseed hfs_rep hv hval_op (s := s)
    dsimp only [whpStepPure]
    cases hfsp : fastStepPure c U n_max θ fs op with
    | some p =>
      rcases p with ⟨fs', res⟩
      rw [hfsp] at hfs_m
      set s_fs := (Memory.spec 0).clientState s
        (fastStepPureGenProg ((mkWhpParams c U V w n_max, base), encodeOpWhp op))
      have hstep : StepSpec w (base + whpSpace c U V w n_max) s prog s_fs (encodeOptRes res) := by
        simp only [prog, whpStepPureGenProg, pure_bind, Prod.mk.eta]
        refine (StepSpec.read hbase_lt).bind ?_
        simp only [hm1, Nat.one_ne_zero, ↓reduceIte, hsp_eq]
        exact StepSpec.bind ⟨rfl, hfs_m.1, hfs_vp⟩ (ite_eq_left rfl ▸ StepSpec.pure _ _)
      rw [hstep.1]
      refine ⟨⟨hth, hfs_m.2.2.1, hfs_m.2.2.2.1⟩, hstep.2.1, hfs_m.2.1, hstep.2.2,
        fun a ha => hfs_m.2.2.2.2 a (hsp_eq ▸ ha), fun _ _ _ => ?_⟩
      unfold whpStepPureGenProg
      simp only [pure_bind, Prod.mk.eta, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hmc_r,
        hcs_r, hcr_r, hm1, Nat.one_ne_zero, ↓reduceIte, hfs_m.1, memoryCost_pure, Nat.add_zero,
        Nat.add_comm 1]
      exact (Nat.add_le_add_right hfs_mc 1).trans (le_max_right _ _)
    | none =>
      rw [hfsp] at hfs_m
      obtain ⟨hseed_fc, hrep_fc, hfr_fc, hvp_fc, hout_fc⟩ :=
        fastToCsrGenProg_spec henv_lg hseed hfs_rep hv (s := s)
      obtain ⟨hcsr_fc, hqv_fc⟩ := hv.fastToCsr_spec
      set s_fc := (Memory.spec 0).clientState s
        (fastToCsrGenProg (mkWhpCoreParams c U V w n_max, base))
      obtain ⟨hfh_rep, hfh_res, hfh_fr, hfh_vp, hfh_out⟩ :=
        fallbackAndHealGenProg_spec henv_lg hseed_fc hrep_fc hcsr_fc hqv_fc hval_op (s := s_fc)
      set s_fh := (Memory.spec 0).clientState s_fc
        (fallbackAndHealGenProg
          (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1), (encodeOpWhp op).2))
      have hstep : StepSpec w (base + whpSpace c U V w n_max) s prog s_fh
          (encodeOptRes (csrStepOp c U n_max θ.1 (fastToCsr n_max fs) op).2) := by
        simp only [prog, whpStepPureGenProg, pure_bind, Prod.mk.eta, hwp1]
        refine (StepSpec.read hbase_lt).bind ?_
        simp only [hm1, Nat.one_ne_zero, ↓reduceIte, hsp_eq]
        refine StepSpec.bind ⟨hfs_m.2, hfs_m.1, hfs_vp⟩ ?_
        simp only [Nat.zero_ne_one, ↓reduceIte]
        exact StepSpec.bind ⟨rfl, rfl, hvp_fc⟩ ⟨rfl, hfh_res, hfh_vp⟩
      rw [hstep.1]
      refine ⟨hfh_rep, hstep.2.1, hfh_fr.trans hfr_fc, hstep.2.2,
        fun a ha => (hfh_out a (hsp_eq ▸ ha)).trans (hout_fc a (hsp_eq ▸ ha)),
        fun _ hst_run hhit => ?_⟩
      simp only [IsFastStepHit, ← hst_run, hfsp, Option.isSome_none, Bool.false_eq_true] at hhit
  | fallback csr =>
    obtain ⟨hth, hseed, hcsr_rep⟩ := hrep
    obtain ⟨_, hcsr, hqv⟩ := hv
    have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := ite_eq_right hth.not_gt
    have hm2 : s.mem base = 2 := by simpa only [hdrMode, Nat.add_zero] using hcsr_rep.1
    have henv_lg : WhpLargeEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hfh_rep, hfh_res, hfh_fr, hfh_vp, hfh_out⟩ :=
      fallbackAndHealGenProg_spec henv_lg hseed hcsr_rep hcsr hqv hval_op (s := s)
    dsimp only [whpStepPure]
    set s_fh := (Memory.spec 0).clientState s
      (fallbackAndHealGenProg
        (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1), (encodeOpWhp op).2))
    have hstep : StepSpec w (base + whpSpace c U V w n_max) s prog s_fh
        (encodeOptRes (csrStepOp c U n_max θ.1 csr op).2) := by
      simp only [prog, whpStepPureGenProg, pure_bind]
      refine (StepSpec.read hbase_lt).bind ?_
      simp only [hm2, Nat.reduceEqDiff, ↓reduceIte, hsp_eq]
      exact ⟨rfl, hfh_res, hfh_vp⟩
    rw [hstep.1]
    exact ⟨hfh_rep, hstep.2.1, hfh_fr, hstep.2.2, fun a ha => hfh_out a (hsp_eq ▸ ha),
      fun _ hst_run hhit => False.elim (by rwa [IsFastStepHit, ← hst_run] at hhit)⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
