/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCode
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic.IntervalCases

/-!
# Distributional Invariant, Initialization, and Query Preservation (`DualEpochDist`)

Defines the 5-regime distributional invariant (`DualDistInv`) across all 12 phases (`0..11`) of the
deamortized dual-epoch resizable succinct dynamic dictionary of
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024], establishes phase-transition classification
and canonical Phase-`8` fibre quotients (`Rel8`, `rep8`), and proves initialization
(`dualDistInv_init`) and read-only query preservation (`dualDistInv_step_query`).

## Main definitions

* `SingleEpochLaw`: uniform epoch-seed law for a single active slot (`ph ≤ 4` or `9 ≤ ph`).
* `DualDistInv`: 5-regime post-prefix distributional invariant (`ph ≤ 4`, `ph = 5`, `ph ∈ {6, 7}`,
  `ph = 8`, `9 ≤ ph`) coupling `DualRep`, `SchedEq`, and independent uniform `SeedWords`.
* `Rel8`, `rep8`: Phase-`8` fibre equivalence and canonical anchor selector.

## Main results

* `dualCoreInv_slot_evs_bounds`, `uniform_seedWords_bad_le`
* `dualDistInv_init`, `dualDistInv_step_query`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open EpochUpdate
open scoped ENNReal

/-! ## Section 1: Slot Equality, Event-Length Bounds, `SingleEpochLaw`, and `DualDistInv` -/

/-- Canonical all-zero `SeedWords c w N` witness for non-emptiness and deterministic slot checks. -/
noncomputable def zeroSeedWords (c w N : ℕ) : SeedWords c w N :=
  fun _ => ⟨0, Nat.two_pow_pos w⟩

private theorem toDictState_injective {U V : ℕ} {s₁ s₂ : Fin U → Option (Fin V)}
    (h : toDictState s₁ = toDictState s₂) : s₁ = s₂ := by
  funext u
  have hu := congrFun h u
  dsimp only [toDictState] at hu
  cases h1 : s₁ u <;> cases h2 : s₂ u <;>
    simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hu
  · rfl
  · exact congrArg some (Fin.ext hu)

theorem slotLatent_eq {c U V : ℕ} {s₁ s₂ : SlotLatent c U V}
    (hn : s₁.nCap = s₂.nCap)
    (habs : toDictState s₁.s_abs = toDictState s₂.s_abs)
    (hseeds : HEq s₁.seeds s₂.seeds)
    (hevs : s₁.evs = s₂.evs) :
    s₁ = s₂ := by
  rcases s₁ with ⟨n1, a1, sd1, ev1⟩
  rcases s₂ with ⟨n2, a2, sd2, ev2⟩
  dsimp only at hn habs hseeds hevs
  subst hn; subst hevs
  have ha : a1 = a2 := toDictState_injective habs
  subst ha
  rw [eq_of_heq hseeds]

private theorem active_elapsed_lt_nDst {isMid : Bool} {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s)
    (hp1 : 1 ≤ s.mem (base + hdrPhase))
    (hd_pos : 0 < s.mem (base + hdrNDst)) :
    L.elapsed + 1 ≤ s.mem (base + hdrNDst) := by
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp1; omega)] at hsched
  have hpost := hsched.post_trig
  have htrig := hsched.trig_cap
  have hb_el := hsched.budget.2.2
  have hnSrc_b := h.nSrc_bounds
  have hnt_U : L.nTrig ≤ U := by
    by_cases hs0 : s.mem (base + hdrNSrc) = 0
    · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.1
    · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.2.2.1
  have hdst_safe := (active_rebuild_safe hpost htrig (Nat.le_add_right _ 0)
    (Nat.le_add_right _ 0) (Nat.zero_le _) hnt_U).2.2.1
  simp only [EpochCapSafe, hd_pos.ne', ↓reduceIte] at hdst_safe
  obtain ⟨hth_d, _, _, hnt_d⟩ := hdst_safe
  by_cases hs0 : s.mem (base + hdrNSrc) = 0
  · rw [hs0, max_eq_left (Nat.zero_le _)] at hb_el
    clear *- hb_el hth_d; omega
  · have hth_s : whpThreshold c ≤ s.mem (base + hdrNSrc) := (hnSrc_b.resolve_left hs0).1
    rw [max_eq_right hth_s] at hb_el
    simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost
    have h27 := hpost.2.2.2.1
    clear *- hb_el h27 hnt_d hd_pos; omega

/-- Every active slot in `DualCoreInv` (`slotSrc` for `ph ≤ 8`, `slotDst` for `8 ≤ ph`) with
positive capacity `0 < sl.nCap` satisfies `sl.evs.length ≤ 4 * sl.nCap` and the prefix live-domain
bound required by `windowOfEvents`. -/
theorem dualCoreInv_slot_evs_bounds {isMid : Bool} {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s) :
    (s.mem (base + hdrPhase) ≤ 8 → 0 < L.slotSrc.nCap →
      L.slotSrc.evs.length ≤ 4 * L.slotSrc.nCap ∧
      ∀ k ≤ L.slotSrc.evs.length,
        (liveDom (EpochUpdate.eval (L.slotSrc.evs.take k))).card ≤ L.slotSrc.nCap) ∧
    (8 ≤ s.mem (base + hdrPhase) → 0 < L.slotDst.nCap →
      L.slotDst.evs.length ≤ 4 * L.slotDst.nCap ∧
      ∀ k ≤ L.slotDst.evs.length,
        (liveDom (EpochUpdate.eval (L.slotDst.evs.take k))).card ≤ L.slotDst.nCap) := by
  refine ⟨fun hle8 hpos => ?_, fun hge8 hpos => ?_⟩
  · by_cases hle7 : s.mem (base + hdrPhase) ≤ 7
    · obtain ⟨hcap, _, hsl, hevs⟩ := h.sl_le7 hle7
      unfold EpochSlotInv at hsl; rw [ite_eq_right hpos.ne'] at hsl
      refine ⟨?_, hsl.2.2.2.1⟩
      by_cases hp0 : s.mem (base + hdrPhase) = 0
      · have hsched := h.sched; rw [ite_eq_left hp0] at hsched
        have hcs : dualCapSrc base s.mem = s.mem (base + hdrNSrc) := by
          unfold dualCapSrc; rw [ite_eq_left hsched.stg_zero]
        have hn_pos : 0 < s.mem (base + hdrNSrc) := hcs ▸ (hcap ▸ hpos)
        have hth : 64 ≤ s.mem (base + hdrNSrc) :=
          (whpThreshold_ge_64 c).trans ((h.nSrc_bounds.resolve_left hn_pos.ne').1)
        obtain ⟨he1, he2⟩ := hsched.ops_evs hn_pos
        rw [hcap, hcs]
        cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] at he1 he2 <;>
          (clear *- he1 he2 hth; omega)
      · have hp1 : 1 ≤ s.mem (base + hdrPhase) := by clear *- hp0; omega
        have hel := active_elapsed_lt_capSrc h hp1 (hcap ▸ hpos)
        have hl := hevs hp1 (hcap ▸ hpos)
        rw [hcap]
        cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] at hl <;>
          (clear *- hl hel; omega)
    · have hp8 : s.mem (base + hdrPhase) = 8 := by clear *- hle8 hle7; omega
      obtain ⟨hcap, _, _, _, _, hsl, _, hevs, _⟩ := h.sl_8 hp8
      unfold EpochSlotInv at hsl; rw [ite_eq_right hpos.ne'] at hsl
      have hl := hevs (hcap ▸ hpos)
      refine ⟨by rw [hcap]; clear *- hl; omega, hsl.2.2.2.1⟩
  · by_cases hp8 : s.mem (base + hdrPhase) = 8
    · obtain ⟨_, hcap, _, _, _, _, hsl, _, hevs⟩ := h.sl_8 hp8
      unfold EpochSlotInv at hsl; rw [ite_eq_right hpos.ne'] at hsl
      have hel := active_elapsed_lt_nDst h (by rw [hp8]; decide) (hcap ▸ hpos)
      have hl := hevs (hcap ▸ hpos)
      refine ⟨?_, hsl.2.2.2.1⟩
      rw [hcap]
      cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] at hl <;>
        (clear *- hl hel; omega)
    · have hp9 : 9 ≤ s.mem (base + hdrPhase) := by clear *- hge8 hp8; omega
      obtain ⟨hcap, _, hsl, hevs⟩ := h.sl_ge9 hp9
      unfold EpochSlotInv at hsl; rw [ite_eq_right hpos.ne'] at hsl
      have hel := active_elapsed_lt_nDst h (by clear *- hp9; omega) (hcap ▸ hpos)
      have hl := hevs (hcap ▸ hpos)
      refine ⟨?_, hsl.2.2.2.1⟩
      rw [hcap]
      cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] at hl <;>
        (clear *- hl hel; omega)

/-- Uniform `SeedWords c w capAct` failure bound for any slot family sharing deterministic capacity
`capAct` and deterministic update log `evs_det`. -/
theorem uniform_seedWords_bad_le {c U V w capAct n_t : ℕ}
    (hUw : Fits w U)
    (hsafe : EpochCapSafe (whpThreshold c) U capAct n_t)
    (evs_det : List (EpochUpdate U V))
    (sl : SeedWords c w capAct → SlotLatent c U V)
    (hcap : ∀ ws, (sl ws).nCap = capAct)
    (hevs : ∀ ws, (sl ws).evs = evs_det)
    (hseeds : 0 < capAct → ∀ ws, HEq (sl ws).seeds (seedsOfWords c U w capAct ws))
    (hbounds : 0 < capAct →
      evs_det.length ≤ 4 * capAct ∧
      ∀ k ≤ evs_det.length, (liveDom (EpochUpdate.eval (evs_det.take k))).card ≤ capAct) :
    (PMF.uniformOfFintype (SeedWords c w capAct)).toOuterMeasure
      {ws | ¬(sl ws).GoodCovers} ≤
      if U < whpThreshold c then 0
      else ((1 : ℝ≥0∞) / 2) * (((max n_t (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
  by_cases hc0 : capAct = 0
  · have hemp : {ws : SeedWords c w capAct | ¬(sl ws).GoodCovers} = ∅ := by
      ext ws; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact SlotLatent.goodCovers_of_small ((hcap ws).trans hc0)
    rw [hemp, MeasureTheory.measure_empty]; exact zero_le
  · have hc_pos : 0 < capAct := Nat.pos_of_ne_zero hc0
    have hs' := hsafe
    simp only [EpochCapSafe, hc0, ↓reduceIte] at hs'
    obtain ⟨hth, hnU, _, _⟩ := hs'
    have hnot_lt : ¬(U < whpThreshold c) := Nat.not_lt.mpr (hth.trans hnU)
    rw [ite_eq_right hnot_lt]
    obtain ⟨hlen, hcard⟩ := hbounds hc_pos
    let win := windowOfEvents hth evs_det hlen hcard
    have hcov := windowCovers_windowOfEvents hth evs_det hlen hcard
    have hsub : {ws : SeedWords c w capAct | ¬(sl ws).GoodCovers} ⊆
        {ws | ¬GoodEpochSeeds win (seedsOfWords c U w capAct ws)} := by
      intro ws hbad hgood
      apply hbad
      have h_sl : sl ws = ⟨capAct, (sl ws).s_abs, seedsOfWords c U w capAct ws, evs_det⟩ := by
        rcases h_eq : sl ws with ⟨nc, sa, sd, ev⟩
        have hnc : nc = capAct := by rw [← hcap ws, h_eq]
        have hev : ev = evs_det := by rw [← hevs ws, h_eq]
        have hsd : HEq sd (seedsOfWords c U w capAct ws) := by
          have hs0 := hseeds hc_pos ws; rwa [h_eq] at hs0
        subst hnc; subst hev; dsimp only; rw [eq_of_heq hsd]
      rw [h_sl]
      exact fun _ => ⟨win, hgood, hcov⟩
    exact ((PMF.uniformOfFintype _).toOuterMeasure.mono hsub).trans
      ((toOuterMeasure_seedWords_not_good_le hth hnU hUw win).trans
        (epochFail_le_half_max_inv_pow hc_pos hsafe))

theorem half_stepFailureProb_le {U : ℕ} (c : ℕ) (s_dict : Dictionary.State U)
    (o : Dynamic.Op U) :
    (if U < whpThreshold c then (0 : ℝ≥0∞)
     else ((1 : ℝ≥0∞) / 2) *
       (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)) ≤
    stepFailureProbWhp c s_dict o := by
  unfold stepFailureProbWhp
  split_ifs with hlt
  · exact le_rfl
  · set p := (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)
    calc ((1 : ℝ≥0∞) / 2) * p
        ≤ ((1 : ℝ≥0∞) / 2) * p + ((1 : ℝ≥0∞) / 2) * p := le_self_add
      _ = p := by rw [← add_mul, ENNReal.add_halves, one_mul]

theorem two_half_stepFailureProb_eq {U : ℕ} (c : ℕ) (s_dict : Dictionary.State U)
    (o : Dynamic.Op U) :
    (if U < whpThreshold c then (0 : ℝ≥0∞)
     else ((1 : ℝ≥0∞) / 2) *
       (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)) +
    (if U < whpThreshold c then (0 : ℝ≥0∞)
     else ((1 : ℝ≥0∞) / 2) *
       (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)) =
    stepFailureProbWhp c s_dict o := by
  unfold stepFailureProbWhp
  split_ifs with hlt
  · exact add_zero 0
  · rw [← add_mul, ENNReal.add_halves, one_mul]

theorem toOuterMeasure_bind_le_const {α β : Type} (μ : PMF α) (f : α → PMF β)
    (S : Set β) (B : ℝ≥0∞) (h : ∀ a ∈ μ.support, (f a).toOuterMeasure S ≤ B) :
    (μ.bind f).toOuterMeasure S ≤ B := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, μ a * (f a).toOuterMeasure S
      ≤ ∑' a, μ a * B := by
        refine tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ μ.support
        · exact mul_le_mul_right (h a ha) (μ a)
        · rw [(PMF.apply_eq_zero_iff μ a).mpr ha, zero_mul, zero_mul]
    _ = B := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

theorem toOuterMeasure_map_pure_le {α β : Type} (μ : PMF α) (g : α → β)
    (BadB : Set β) (GoodA : α → Prop)
    (himp : ∀ a, GoodA a → g a ∉ BadB) :
    (μ.bind fun a => PMF.pure (g a)).toOuterMeasure BadB ≤
      μ.toOuterMeasure {a | ¬GoodA a} := by
  have heq : (μ.bind fun a => PMF.pure (g a)) = μ.map g := by unfold PMF.map; rfl
  rw [heq, PMF.toOuterMeasure_map_apply]
  exact μ.toOuterMeasure.mono fun a hbad hgood => himp a hgood hbad

/-- Uniform single-epoch seed law for the sole active slot (`isDst = false` in Phases `0..4`,
`isDst = true` in Phases `9..11`). -/
@[expose]
def SingleEpochLaw (c U V w base : ℕ) (s_dict : Dictionary.State U) (s_rep : Memory.State)
    (capAct : ℕ) (isDst : Bool) (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ (α : Type) (μ_idx : PMF α)
    (evs_of : α → List (EpochUpdate U V))
    (f_act : α → SeedWords c w capAct → LatentRState (DualLatent c U V) rWhp),
    ν = μ_idx.bind (fun a => (PMF.uniformOfFintype (SeedWords c w capAct)).map (f_act a)) ∧
    ∀ a ∈ μ_idx.support, ∀ ws : SeedWords c w capAct,
      let t := f_act a ws
      let sl := if isDst then t.latent.slotDst else t.latent.slotSrc
      DualRep c U V w base s_dict t.latent t.data ∧
      SchedEq base s_rep (rMemState t.data) ∧
      sl.nCap = capAct ∧
      sl.evs = evs_of a ∧
      (0 < capAct → HEq sl.seeds (seedsOfWords c U w capAct ws))

/-- When `capAct = 0`, any distribution `ν` supported on `DualRep` states sharing `SchedEq` with
`s_rep` and `sl.nCap = 0` satisfies `SingleEpochLaw`. -/
theorem singleEpochLaw_zero {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {s_rep : Memory.State} {isDst : Bool} {ν : PMF (LatentRState (DualLatent c U V) rWhp)}
    (hsupp : ∀ t ∈ ν.support,
      DualRep c U V w base s_dict t.latent t.data ∧
      SchedEq base s_rep (rMemState t.data) ∧
      (if isDst then t.latent.slotDst else t.latent.slotSrc).nCap = 0) :
    SingleEpochLaw c U V w base s_dict s_rep 0 isDst ν := by
  refine ⟨LatentRState (DualLatent c U V) rWhp, ν,
    fun t => (if isDst then t.latent.slotDst else t.latent.slotSrc).evs,
    fun t _ => t, ?_, fun t ht _ => ?_⟩
  · conv_lhs => rw [← PMF.bind_pure ν]
    refine congrArg (ν.bind ·) (funext fun t => ?_)
    rw [uniformOfFintype_seedWords_zero c w, PMF.pure_map]
  · obtain ⟨hr, hsch, hnc⟩ := hsupp t ht
    exact ⟨hr, hsch, hnc, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩

/-- Phase-`5` distributional law coupling uniform `slotSrc` seeds (`SeedWords c w capSrc`) with an
independent uniform prefix `(Fin k_pre → Fin (2 ^ w))` of `slotDst` random-fill words. -/
@[expose]
def Ph5Law (c U V w base : ℕ) (s_dict : Dictionary.State U) (s_rep : Memory.State)
    (capSrc : ℕ) (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ (α : Type) (μ_idx : PMF α) (k_pre : ℕ)
    (evs_src : α → List (EpochUpdate U V))
    (L_anc : α → SeedWords c w capSrc → DualLatent c U V)
    (s_anc : α → SeedWords c w capSrc → Memory.State)
    (f5 : α → SeedWords c w capSrc → (Fin k_pre → Fin (2 ^ w)) →
      LatentRState (DualLatent c U V) rWhp),
    ν = μ_idx.bind (fun a =>
      (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
        (PMF.uniformOfFintype (Fin k_pre → Fin (2 ^ w))).map (f5 a ws_src))) ∧
    ∀ a ∈ μ_idx.support, ∀ ws_src : SeedWords c w capSrc,
      DualStateInv c U V w base s_dict (L_anc a ws_src) (s_anc a ws_src) ∧
      SchedEq base s_rep (s_anc a ws_src) ∧
      (L_anc a ws_src).slotSrc.nCap = capSrc ∧
      (L_anc a ws_src).slotSrc.evs = evs_src a ∧
      (0 < capSrc → HEq (L_anc a ws_src).slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
      ∀ ws_pre : Fin k_pre → Fin (2 ^ w),
        let t := f5 a ws_src ws_pre
        DualRep c U V w base s_dict t.latent t.data ∧
        Ph5StateAt c w base (s_anc a ws_src) k_pre ws_pre (rMemState t.data) ∧
        t.latent.slotSrc = (L_anc a ws_src).slotSrc

/-- Phases-`6..7` distributional law coupling independent uniform `slotSrc` and `slotDst` seeds via
`Coupled67` before `slotDst` begins receiving updates. -/
@[expose]
def Coupled67Law (c U V w base : ℕ) (s_dict : Dictionary.State U) (s_rep : Memory.State)
    (capSrc capDst : ℕ) (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ (α : Type) (μ_idx : PMF α)
    (evs_src : α → List (EpochUpdate U V))
    (L_anc : α → SeedWords c w capSrc → DualLatent c U V)
    (s_anc : α → SeedWords c w capSrc → Memory.State)
    (f67 : α → SeedWords c w capSrc → SeedWords c w capDst →
      LatentRState (DualLatent c U V) rWhp),
    ν = μ_idx.bind (fun a =>
      (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
        (PMF.uniformOfFintype (SeedWords c w capDst)).map (f67 a ws_src))) ∧
    ∀ a ∈ μ_idx.support, ∀ ws_src : SeedWords c w capSrc,
      DualStateInv c U V w base s_dict (L_anc a ws_src) (s_anc a ws_src) ∧
      SchedEq base s_rep (s_anc a ws_src) ∧
      (L_anc a ws_src).slotSrc.nCap = capSrc ∧
      (L_anc a ws_src).slotSrc.evs = evs_src a ∧
      (0 < capSrc → HEq (L_anc a ws_src).slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
      ∀ ws_dst : SeedWords c w capDst,
        let t := f67 a ws_src ws_dst
        DualRep c U V w base s_dict t.latent t.data ∧
        Coupled67 c w base (s_anc a ws_src) (rMemState t.data) ∧
        t.latent.slotSrc = (L_anc a ws_src).slotSrc ∧
        (0 < capDst →
          t.latent.slotDst.nCap = capDst ∧
          t.latent.slotDst.evs = [] ∧
          HEq t.latent.slotDst.seeds (seedsOfWords c U w capDst ws_dst))

/-- Phase-`8` distributional law coupling independent uniform `slotSrc` and `slotDst` seeds via
`Coupled8` across incremental migration Drain. -/
@[expose]
def Coupled8Law (c U V w base : ℕ) (s_dict : Dictionary.State U) (s_rep : Memory.State)
    (capSrc capDst : ℕ) (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ (α : Type) (μ_idx : PMF α)
    (evs_src : α → List (EpochUpdate U V))
    (evs_dst : α → SeedWords c w capSrc → List (EpochUpdate U V))
    (L_anc : α → SeedWords c w capSrc → DualLatent c U V)
    (s_anc : α → SeedWords c w capSrc → Memory.State)
    (f8 : α → SeedWords c w capSrc → SeedWords c w capDst →
      LatentRState (DualLatent c U V) rWhp),
    ν = μ_idx.bind (fun a =>
      (PMF.uniformOfFintype (SeedWords c w capSrc)).bind (fun ws_src =>
        (PMF.uniformOfFintype (SeedWords c w capDst)).map (f8 a ws_src))) ∧
    ∀ a ∈ μ_idx.support, ∀ ws_src : SeedWords c w capSrc,
      DualStateInv c U V w base s_dict (L_anc a ws_src) (s_anc a ws_src) ∧
      SchedEq base s_rep (s_anc a ws_src) ∧
      (L_anc a ws_src).slotSrc.nCap = capSrc ∧
      (L_anc a ws_src).slotSrc.evs = evs_src a ∧
      (0 < capSrc → HEq (L_anc a ws_src).slotSrc.seeds (seedsOfWords c U w capSrc ws_src)) ∧
      (L_anc a ws_src).slotDst.evs = evs_dst a ws_src ∧
      ∀ ws_dst : SeedWords c w capDst,
        let t := f8 a ws_src ws_dst
        DualRep c U V w base s_dict t.latent t.data ∧
        Coupled8 c V w base (Dictionary.dom s_dict).card (s_anc a ws_src) (rMemState t.data) ∧
        t.latent.slotSrc = (L_anc a ws_src).slotSrc ∧
        t.latent.slotDst.nCap = capDst ∧
        t.latent.slotDst.s_abs = (L_anc a ws_src).slotDst.s_abs ∧
        t.latent.slotDst.evs = evs_dst a ws_src ∧
        (0 < capDst → HEq t.latent.slotDst.seeds (seedsOfWords c U w capDst ws_dst))

/-- 5-regime distributional invariant on `ν : PMF (LatentRState (DualLatent c U V) rWhp)` across
phases `0..4`, `5`, `6..7`, `8`, and `9..11`. -/
@[expose]
def DualDistInv (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (ν : PMF (LatentRState (DualLatent c U V) rWhp)) : Prop :=
  ∃ (L_rep : DualLatent c U V) (s_rep : Memory.State),
    DualStateInv c U V w base s_dict L_rep s_rep ∧
    let ph := s_rep.mem (base + hdrPhase)
    let capSrc := dualCapSrc base s_rep.mem
    let capDst := s_rep.mem (base + hdrNDst)
    if ph ≤ 4 then
      SingleEpochLaw c U V w base s_dict s_rep capSrc false ν
    else if ph = 5 then
      Ph5Law c U V w base s_dict s_rep capSrc ν
    else if ph = 6 ∨ ph = 7 then
      Coupled67Law c U V w base s_dict s_rep capSrc capDst ν
    else if ph = 8 then
      Coupled8Law c U V w base s_dict s_rep capSrc capDst ν
    else
      SingleEpochLaw c U V w base s_dict s_rep capDst true ν

/-! ## Section 2: Phase-Transition Classification, Deterministic Lifter, and Phase-`8` Quotient -/

theorem dualCapSrc_safe {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s) :
    EpochCapSafe (whpThreshold c) U (dualCapSrc base s.mem) (Dictionary.dom s_dict).card := by
  obtain ⟨hs, hd⟩ := dualCoreInv_cap_safe h
  unfold dualCapSrc
  by_cases hst0 : s.mem (base + hdrStage) = 0
  · rw [ite_eq_left hst0]; exact hs
  · rw [ite_eq_right hst0]
    have hph_ne0 : s.mem (base + hdrPhase) ≠ 0 := by
      intro hp0; have hsched := h.sched; rw [ite_eq_left hp0] at hsched
      exact hst0 hsched.stg_zero
    rwa [ite_eq_right hph_ne0] at hd

theorem dualNDst_safe {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s) (hp0 : s.mem (base + hdrPhase) ≠ 0) :
    EpochCapSafe (whpThreshold c) U (s.mem (base + hdrNDst)) (Dictionary.dom s_dict).card := by
  have hd := (dualCoreInv_cap_safe h).2
  rwa [ite_eq_right hp0] at hd

theorem dualPreShrinkInv_hdr_w {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s_pre : Memory.State}
    (h : DualPreShrinkInv c U V w base s_dict L s_pre) :
    s_pre.mem (base + hdrW) = w := by
  have hbr := h.2.2.2
  split_ifs at hbr with h1 h2 h3
  · exact hbr.2.2.hdr.2.2.1
  · exact hbr.2.hdr.2.2.1
  · exact hbr.2.2.hdr.2.2.1
  · by_cases hle :
        s_pre.frontier -
          (s_pre.mem (base + hdrItemLo) +
            pairStreamWords (Dictionary.dom s_dict).card (s_pre.mem (base + hdrQLo))
              (valBits V) w) ≤ bulkBatchWhp
    · exact (hbr.2.2.2 hle).1.hdr.2.2.1
    · exact (hbr.2.2.1 (Nat.not_le.mp hle)).hdr.2.2.1

/-- Classifies the post-tick / post-shrink phase `ph'` starting from a `DualMidInv` state with
`s_mid.mem (base + hdrPhase) ≤ 4`: either `ph' ≤ 4`, `ph' = 5 ∧ cur' = 32`, or
`ph' = 6 ∧ nDst' = 0` (and in all three cases `s_tick.mem (base + hdrPhase) ≠ 11`). -/
theorem bgTick_post_from_le4 {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L_mid L' L_post : DualLatent c U V} {s_mid : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hmid : DualMidInv c U V w base s_dict L_mid s_mid)
    (hle4 : s_mid.mem (base + hdrPhase) ≤ 4)
    (hpre : DualPreShrinkInv c U V w base s_dict L'
      ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))))
    (hinv_post : DualStateInv c U V w base s_dict L_post
      { mem := clear
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag))).mem
          (((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)))
          ((Memory.spec 0).clientResult
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag)))
        frontier :=
          ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)) }) :
    let s_tick := (Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))
    let s_ps := (Memory.spec 0).clientState s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_post : Memory.State :=
      { mem := clear s_ps.mem (s_tick.frontier - k_sh) k_sh, frontier := s_tick.frontier - k_sh }
    s_tick.mem (base + hdrPhase) ≠ 11 ∧
    (s_post.mem (base + hdrPhase) ≤ 4 ∨
      (s_post.mem (base + hdrPhase) = 5 ∧ s_post.mem (base + hdrCur) = 32) ∨
      (s_post.mem (base + hdrPhase) = 6 ∧ s_post.mem (base + hdrNDst) = 0)) := by
  intro s_tick s_ps k_sh s_post
  have hw_pos : 0 < w := by have := hmid.hw11; omega
  have htick_cls :
      s_tick.mem (base + hdrPhase) ≤ 4 ∨
      (s_tick.mem (base + hdrPhase) = 5 ∧ s_tick.mem (base + hdrCur) = 32) ∨
      (s_tick.mem (base + hdrPhase) = 6 ∧ s_tick.mem (base + hdrNDst) = 0) := by
    have hbgev := (bgTickProg_eval base s_mid.frontier s_mid).1
    dsimp only at hbgev
    change s_tick = _ at hbgev
    interval_cases hp_val : s_mid.mem (base + hdrPhase)
    · simp only [↓reduceIte] at hbgev
      rw [hbgev, (tickIdleProg_eval base s_mid).1]
      split_ifs <;> dsimp only <;>
        first
        | (rw [Function.update_of_ne (base_add_ne (by decide)), hp_val]; exact Or.inl (by decide))
        | (rw [Function.update_self]; exact Or.inl (by decide))
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev, (tickLogProg_eval base s_mid).1]
      by_cases hs2 : s_mid.mem (base + hdrLogSub) < 2
      · rw [ite_eq_left hs2]
        have hsched := hmid.sched; rw [ite_eq_right (by rw [hp_val]; decide)] at hsched
        have hnD_pos := (hsched.ph1 hp_val).2.1
        have hth_d := (hsched.nDst_bounds.resolve_left hnD_pos.ne').1
        have hnD_ge2 : 2 ≤ s_mid.mem (base + hdrNDst) :=
          (by decide : 2 ≤ 2 ^ 20).trans ((whpThreshold_ge_pow20 c).trans hth_d)
        have hlog_inv : ¬(1 < s_mid.mem (base + hdrLogAcc)) → s_mid.mem (base + hdrLogSub) = 0 →
            s_mid.mem (base + hdrLogK) = Nat.log 2 (s_mid.mem (base + hdrNDst)) := by
          intro hna hs0
          obtain ⟨_, h0, _, _⟩ := hmid.ph1_inv hp_val
          obtain ⟨h1_a, hlo, hhi⟩ := h0 hs0
          have ha1 : s_mid.mem (base + hdrLogAcc) = 1 := by omega
          rw [ha1, one_mul] at hlo; rw [ha1] at hhi
          exact le_antisymm (Nat.le_log_of_pow_le Nat.one_lt_two hlo)
            (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega)
              (by rw [Nat.pow_succ]; omega)))
        rw [(tickLogShiftProg_eval s_mid hnD_ge2 hlog_inv).1]
        split_ifs <;> dsimp only
        · iterate 2 rw [Function.update_of_ne (base_add_ne (by decide))]
          rw [hp_val]; exact Or.inl (by decide)
        · iterate 7 rw [Function.update_of_ne (base_add_ne (by decide))]
          rw [hp_val]; exact Or.inl (by decide)
        · iterate 2 rw [Function.update_of_ne (base_add_ne (by decide))]
          rw [hp_val]; exact Or.inl (by decide)
      · rw [ite_eq_right hs2, (tickLogFinishProg_eval base s_mid).1]; dsimp only
        rw [Function.update_self]; exact Or.inl (by decide)
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      have hw_m : 0 < s_mid.mem (base + hdrW) := hmid.hdr.2.2.1 ▸ hw_pos
      rw [hbgev, (tickGrowPreProg_eval hw_m).1]
      split_ifs
      · rw [hp_val]; exact Or.inl (by decide)
      · dsimp only; rw [Function.update_self]; exact Or.inl (by decide)
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev, (tickSlideUpProg_eval base s_mid).1]
      let cfg : SplitPairCfg :=
        { baseLo := s_mid.mem (base + hdrItemLo), qBitsLo := s_mid.mem (base + hdrQLo),
          vBitsLo := valBits V, baseHi := s_mid.mem (base + hdrItemHi),
          qBitsHi := s_mid.mem (base + hdrQHi), vBitsHi := valBits V, w := w }
      have hctx : (Memory.spec 0).clientResult s_mid (loadSplitPairCtxProg base) = cfg.toCtx := by
        rw [(loadSplitPairCtxProg_eval base s_mid).2.1]
        dsimp only [cfg, SplitPairCfg.toCtx]; rw [hmid.hdr.2.2.2.2.1, hmid.hdr.2.2.1]
      have hsched := hmid.sched; rw [ite_eq_right (by rw [hp_val]; decide)] at hsched
      obtain ⟨_, hpad_e, _, _, hibHi_e, hqHi_e⟩ := hsched.ge2 (by rw [hp_val]; decide)
      have hibLo_e := hsched.ibLo_eq; rw [hp_val, ite_eq_left (by decide : 3 < 10)] at hibLo_e
      have hqLo_e := hsched.qLo_eq; rw [hp_val, ite_eq_left (by decide : 3 < 10)] at hqLo_e
      have hq_le : cfg.qBitsLo ≤ cfg.qBitsHi := by
        dsimp only [cfg]; rw [hqHi_e, hqLo_e]; exact le_max_left _ _
      have hib_le : cfg.baseLo + 4 ≤ cfg.baseHi := by
        dsimp only [cfg]
        have hm_le : s_mid.mem (base + hdrMSrc) ≤ s_mid.mem (base + hdrPad) := by
          rw [hpad_e]; exact le_max_left _ _
        rw [hibHi_e, hibLo_e]; split_ifs <;> omega
      obtain ⟨_, hvb_w, hqLo_w, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits hmid
      have hcfg_v : cfg.Valid w (Dictionary.dom s_dict).card s_mid.frontier :=
        ⟨hw_pos, rfl, hqLo_w, hvb_w, hqHi_w, hvb_w,
          by dsimp only [cfg] at hq_le ⊢; omega, by dsimp only [cfg] at hib_le ⊢; omega,
          lt_of_le_of_lt hmid.live_le hmid.U_lt,
          (hsched.ph3_10 ⟨by rw [hp_val], by rw [hp_val]; decide⟩).1⟩
      obtain ⟨_, _, _, _, _, hout_sb⟩ := slideUpBatchProg_spec (cfg := cfg)
        (n_tot := (Dictionary.dom s_dict).card) (s_split := s_mid.mem (base + hdrSplit))
        (s := s_mid) hcfg_v hq_le le_rfl (hmid.ph3_inv hp_val).1 itemBatchWhp
      have hibLo_192 : base + 192 ≤ cfg.baseLo := by dsimp only [cfg]; rw [hibLo_e]; omega
      rw [hctx]
      split_ifs with hsp0 hd0
      · refine Or.inr (Or.inr ⟨by dsimp only; rw [Function.update_self], ?_⟩)
        dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (by dsimp only [hdrSmallMeta1, hdrNDst]; omega),
          Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide)),
          (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + hdrNDst)
            (by dsimp only [hdrPBase0, hdrNDst]; omega)]
        dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hout_sb (base + hdrNDst) (by dsimp only [hdrNDst]; omega)]
        exact hd0
      · dsimp only; rw [Function.update_self]; exact Or.inl (by decide)
      · dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hout_sb (base + hdrPhase) (by dsimp only [hdrPhase]; omega), hp_val]
        exact Or.inl (by decide)
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev, (tickZeroMetaProg_eval base s_mid).1]
      obtain ⟨hd_pos, hcur_le, _⟩ := hmid.ph4_inv hp_val
      have hsched := hmid.sched; rw [ite_eq_right (by rw [hp_val]; decide)] at hsched
      obtain ⟨hmD_e, hpad_e, _, _, hibHi_e, _⟩ := hsched.ge2 (by rw [hp_val]; decide)
      have hth_d := (hsched.nDst_bounds.resolve_left hd_pos.ne').1
      obtain ⟨h32, hfp, hbm, hod⟩ := epochMeta_offsets_le (w := w) hth_d
      have hm32 : 32 ≤ s_mid.mem (base + hdrMDst) :=
        (h32.trans (hfp.trans (hbm.trans hod))).trans hmD_e.symm.le
      have hmD_p : s_mid.mem (base + hdrMDst) ≤ s_mid.mem (base + hdrPad) := by
        rw [hpad_e]; exact le_max_right _ _
      set metaDst := if s_mid.mem (base + hdrStage) = 0 then
        base + 192 + s_mid.mem (base + hdrPad) else base + 192
      have hmd_fr : metaDst + s_mid.mem (base + hdrMDst) ≤ s_mid.frontier := by
        have hhi := (hsched.ph3_10 ⟨by rw [hp_val]; decide, by rw [hp_val]; decide⟩).1
        rw [hibHi_e, ite_eq_right hd_pos.ne'] at hhi
        dsimp only [metaDst]; split_ifs <;> omega
      obtain ⟨_, _, _, _, hmem_zb⟩ := zeroWordsBatchProg_spec hw_pos hcur_le
        (by omega : metaDst < s_mid.frontier) hmd_fr bulkBatchWhp
      by_cases hlt_zb : (Memory.spec 0).clientResult s_mid
          (zeroWordsBatchProg (((metaDst, s_mid.mem (base + hdrMDst)),
            s_mid.mem (base + hdrCur)), bulkBatchWhp)) < s_mid.mem (base + hdrMDst)
      · rw [ite_eq_left hlt_zb]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)), hmem_zb,
          ite_eq_right (by dsimp only [metaDst, hdrPhase]; split_ifs <;> omega), hp_val]
        exact Or.inl (by decide)
      · rw [ite_eq_right hlt_zb]; dsimp only
        refine Or.inr (Or.inl ⟨by rw [Function.update_self], ?_⟩)
        rw [Function.update_of_ne (base_add_ne (by decide)), Function.update_self]
  have hne11 : s_tick.mem (base + hdrPhase) ≠ 11 := by
    rcases htick_cls with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hw_t := dualPreShrinkInv_hdr_w hpre
  have hnot_rf : ¬(s_tick.mem (base + hdrPhase) = 5 ∧
      s_tick.mem ((if s_tick.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) + 31) ≤ s_tick.mem (base + hdrCur)) := by
    rintro ⟨hp5, hle⟩
    have hpD : (if s_tick.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        dualPDst base s_tick.mem := by
      unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
    rw [hpD] at hle
    exact absurd (lt_of_lt_of_le (hpre.2.2.1 hp5) hle) (Nat.lt_irrefl _)
  have hs_ps_eq : s_ps = s_tick := by
    dsimp only [s_ps]
    rw [(postRandShrinkProg_eval base s_tick.frontier opTag s_tick).1]
    dsimp only
    rw [ite_eq_right hop_nz, ite_eq_right hnot_rf,
      (calcPostShrinkProg_eval (curFr := s_tick.frontier) (hw_t ▸ hw_pos)).1]
    dsimp only
    rw [ite_eq_right (fun h => hne11 h.1)]
  have hb192 : base + 192 ≤ s_tick.frontier - k_sh := hinv_post.base_fr
  have hmem_low : ∀ off < 48, s_post.mem (base + off) = s_tick.mem (base + off) :=
    fun off hoff => by
      dsimp only [s_post]
      rw [hs_ps_eq, clear_of_not_owns (by simp only [Block.Owns]; omega)]
  rw [hmem_low hdrPhase (by decide), hmem_low hdrCur (by decide), hmem_low hdrNDst (by decide)]
  exact ⟨hne11, htick_cls⟩

/-- Classifies the post-tick / post-shrink phase `ph'` starting from a `DualMidInv` state with
`9 ≤ s_mid.mem (base + hdrPhase)`:
1. `ph = 9 ∧ s_tick.ph = 4 ∧ ph' = 4 ∧ s_tick.ph ≠ 11` (`Stage B` promotion `slotDst → slotSrc`),
2. `ph ≠ 9 ∨ s_tick.ph ≠ 4`, `s_tick.ph = 11 ∧ s_ps.ph = 0 ∧ ph' = 0` (`11 → 0` promotion), or
3. neither promotion fired, `9 ≤ ph'`, and
   `s_post.mem (base + hdrNDst) = s_mid.mem (base + hdrNDst)`.
-/
theorem bgTick_post_from_ge9 {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L_mid L' L_post : DualLatent c U V} {s_mid : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hmid : DualMidInv c U V w base s_dict L_mid s_mid)
    (hge9 : 9 ≤ s_mid.mem (base + hdrPhase))
    (hpre : DualPreShrinkInv c U V w base s_dict L'
      ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))))
    (hinv_post : DualStateInv c U V w base s_dict L_post
      { mem := clear
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag))).mem
          (((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)))
          ((Memory.spec 0).clientResult
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag)))
        frontier :=
          ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)) }) :
    let s_tick := (Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))
    let s_ps := (Memory.spec 0).clientState s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_post : Memory.State :=
      { mem := clear s_ps.mem (s_tick.frontier - k_sh) k_sh, frontier := s_tick.frontier - k_sh }
    let p1 := s_mid.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4
    let p2 := s_tick.mem (base + hdrPhase) = 11 ∧ s_ps.mem (base + hdrPhase) = 0
    (p1 ∧ ¬p2 ∧ s_post.mem (base + hdrPhase) = 4) ∨
    (¬p1 ∧ p2 ∧ s_post.mem (base + hdrPhase) = 0) ∨
    (¬p1 ∧ ¬p2 ∧ 9 ≤ s_post.mem (base + hdrPhase) ∧
      s_post.mem (base + hdrNDst) = s_mid.mem (base + hdrNDst)) := by
  intro s_tick s_ps k_sh s_post p1 p2
  have hw_pos : 0 < w := by have := hmid.hw11; omega
  have hph_le : s_mid.mem (base + hdrPhase) ≤ 11 := hmid.ph_le
  have htick_cls :
      (s_mid.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) ∨
      (9 ≤ s_tick.mem (base + hdrPhase) ∧
        s_tick.mem (base + hdrNDst) = s_mid.mem (base + hdrNDst)) := by
    have hbgev := (bgTickProg_eval base s_mid.frontier s_mid).1
    dsimp only at hbgev; change s_tick = _ at hbgev
    interval_cases hp_val : s_mid.mem (base + hdrPhase)
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev, (tickUnpermProg_eval base s_mid).1]
      have hs1_pres : ∀ k < 48, k ≠ hdrUnpermDone →
          (if s_mid.mem (base + hdrUnpermDone) = 0 then
             (Memory.spec 0).clientState s_mid (stepUnpermBatchProg base)
           else s_mid).mem (base + k) = s_mid.mem (base + k) := by
        intro k hk hne
        by_cases hd0 : s_mid.mem (base + hdrUnpermDone) = 0
        · rw [ite_eq_left hd0]
          obtain ⟨_, _, _, _, hctx, _, _, _, _⟩ :=
            dualPgHost_eval_valid hmid (by rw [hp_val]; decide) (by rw [hp_val]; decide)
          have hdisj := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) hmid
            (by rw [hp_val]; decide) (by rw [hp_val])
          have hsched := hmid.sched; rw [ite_eq_right (by rw [hp_val]; decide)] at hsched
          obtain ⟨_, _, _, _, hibHi_e, _⟩ := hsched.ge2 (by rw [hp_val]; decide)
          have hibHi_ge : base + 196 ≤ s_mid.mem (base + hdrItemHi) := by
            rw [hibHi_e]; split_ifs <;> omega
          set pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s_mid.mem
          have hub_frm := pageRunUnpermBatchProg_frame (L := pgH) hw_pos itemBatchWhp
          have hev_sub := (stepUnpermBatchProg_eval base s_mid).1
          simp only [hctx] at hev_sub
          rw [hev_sub]
          set s2 := (Memory.spec 0).clientState s_mid
            (pageRunUnpermBatchProg (pgH.toCtx, itemBatchWhp))
          have hs2_k : s2.mem (base + k) = s_mid.mem (base + k) :=
            hub_frm.mem_outside s_mid (base + k) fun hpg => by
              rcases hpg with h_m | h_i
              · have h210 := (hdisj (base + k) h_m).1; omega
              · have hi1 : s_mid.mem (base + hdrItemHi) ≤ base + k := h_i.1; omega
          by_cases hc4 : s2.mem ((PageArenaLayout.ofCtx pgH.toCtx).metaBase + 18) = 4
          · rw [ite_eq_left hc4]; dsimp only
            rw [Function.update_of_ne (base_add_ne hne), (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
              (setSlotIoProg_frame _ _).mem_outside _ (base + k)
                (by dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
            exact hs2_k
          · rw [ite_eq_right hc4]; exact hs2_k
        · rw [ite_eq_right hd0]
      set s1 := if s_mid.mem (base + hdrUnpermDone) = 0 then
        (Memory.spec 0).clientState s_mid (stepUnpermBatchProg base) else s_mid
      by_cases hr1 : 1 < s_mid.mem (base + hdrRem)
      · rw [ite_eq_left hr1]; dsimp only
        refine Or.inr ⟨?_, ?_⟩
        · rw [Function.update_of_ne (base_add_ne (by decide)),
            hs1_pres hdrPhase (by decide) (by decide), hp_val]
        · rw [Function.update_of_ne (base_add_ne (by decide)),
            hs1_pres hdrNDst (by decide) (by decide)]
      · rw [ite_eq_right hr1, (finishUnpermProg_eval base s1).1]; dsimp only
        by_cases hc : s1.mem (base + hdrStage) = 0 ∧ 0 < s1.mem (base + hdrNDst)
        · rw [ite_eq_left hc]
          exact Or.inl ⟨rfl, by dsimp only; rw [Function.update_self]⟩
        · rw [ite_eq_right hc]
          refine Or.inr ⟨by dsimp only; rw [Function.update_self]; decide, ?_⟩
          dsimp only
          rw [Function.update_of_ne (base_add_ne (by decide)),
            (setSplitSlotIoProg_eval _ _ _ _).1,
            (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + hdrNDst)
              (by dsimp only [hdrPBase0, hdrNDst]; omega)]
          dsimp only
          iterate 3 rw [Function.update_of_ne (base_add_ne (by decide))]
          by_cases hst0 : s1.mem (base + hdrStage) = 0
          · rw [ite_eq_left hst0]
            iterate 4 rw [Function.update_of_ne
              (by dsimp only [hdrSmallMeta0, hdrPBase0, hdrNDst]; omega)]
            exact hs1_pres hdrNDst (by decide) (by decide)
          · rw [ite_eq_right hst0]
            exact hs1_pres hdrNDst (by decide) (by decide)
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev, (tickSlideDownProg_eval base s_mid).1]
      let cfg : SplitPairCfg :=
        { baseLo := s_mid.mem (base + hdrItemLo), qBitsLo := s_mid.mem (base + hdrQLo),
          vBitsLo := valBits V, baseHi := s_mid.mem (base + hdrItemHi),
          qBitsHi := s_mid.mem (base + hdrQHi), vBitsHi := valBits V, w := w }
      have hctx : (Memory.spec 0).clientResult s_mid (loadSplitPairCtxProg base) = cfg.toCtx := by
        rw [(loadSplitPairCtxProg_eval base s_mid).2.1]
        dsimp only [cfg, SplitPairCfg.toCtx]; rw [hmid.hdr.2.2.2.2.1, hmid.hdr.2.2.1]
      have hsched := hmid.sched; rw [ite_eq_right (by rw [hp_val]; decide)] at hsched
      obtain ⟨hmD_e, _, _, _, hibHi_e, hqHi_e⟩ := hsched.ge2 (by rw [hp_val]; decide)
      have hibLo_e := hsched.ibLo_eq; rw [hp_val, ite_eq_right (by decide : ¬(10 < 10))] at hibLo_e
      have hqLo_e := hsched.qLo_eq; rw [hp_val, ite_eq_right (by decide : ¬(10 < 10))] at hqLo_e
      obtain ⟨_, hvb_w, hqLo_w, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits hmid
      obtain ⟨hsp_le, hhi_quot⟩ := hmid.ph10_inv hp_val
      obtain ⟨_, hdict_d, hsl_d, _⟩ := hmid.sl_ge9 (by rw [hp_val]; decide)
      have hfr_hi_lo := (hsched.ph3_10 ⟨by rw [hp_val]; decide, by rw [hp_val]⟩).1
      have hq_le : s_mid.mem (base + hdrQLo) ≤ s_mid.mem (base + hdrQHi) := by
        rw [hqHi_e, hqLo_e]; exact le_max_right _ _
      have hib_le : s_mid.mem (base + hdrItemLo) + 4 ≤ s_mid.mem (base + hdrItemHi) := by
        rw [hibHi_e, hibLo_e]
        by_cases hdz : s_mid.mem (base + hdrNDst) = 0
        · rw [ite_eq_left hdz]
          have hm0 : s_mid.mem (base + hdrMDst) = 0 := by
            rw [hmD_e, hdz]; exact epochMetaWordsWhp_zero_eq c w
          rw [hm0]; omega
        · rw [ite_eq_right hdz]; omega
      have hcfg_v : cfg.Valid w (Dictionary.dom s_dict).card s_mid.frontier :=
        ⟨hw_pos, rfl, hqLo_w, hvb_w, hqHi_w, hvb_w,
          by dsimp only [cfg]; omega, by dsimp only [cfg]; omega,
          lt_of_le_of_lt hmid.live_le hmid.U_lt, hfr_hi_lo⟩
      set io_sp := splitSlotIo w (valBits V) base (s_mid.mem (base + hdrItemLo))
        (s_mid.mem (base + hdrQLo)) (s_mid.mem (base + hdrItemHi)) (s_mid.mem (base + hdrQHi))
        (Dictionary.dom s_dict).card
      have hpD_s : dualPDst base s_mid.mem = base + hdrPBase0 := by
        unfold dualPDst; rw [hp_val, ite_eq_right (by decide : ¬(10 < 10))]
      have hio_d10 : activeDstIo c w (valBits V) base (s_mid.mem (base + hdrStage))
          (s_mid.mem (base + hdrPhase)) (s_mid.mem (base + hdrNSrc)) (s_mid.mem (base + hdrNDst))
          (s_mid.mem (base + hdrPad)) (s_mid.mem (base + hdrItemLo)) (s_mid.mem (base + hdrQLo))
          (s_mid.mem (base + hdrItemHi)) (s_mid.mem (base + hdrQHi))
          (Dictionary.dom s_dict).card (s_mid.mem (base + hdrUnpermDone)) = io_sp := by
        rw [hp_val]; unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
      have hsl_d0 : EpochSlotInv c U V w s_mid.frontier (base + hdrPBase0)
          (dualMbDst base s_mid.mem)
          io_sp 0 false L_mid.slotDst s_mid.mem := by
        rw [hpD_s, hio_d10] at hsl_d
        simpa only [hp_val, Nat.reduceEqDiff, false_and, and_false, ↓reduceIte] using hsl_d
      have hns_d : s_mid.mem (dualMbDst base s_mid.mem + 1) = (Dictionary.dom s_dict).card := by
        rw [hsl_d0.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
      have hfit : ∀ d, s_mid.mem (base + hdrSplit) ≤ d →
          d < min (Dictionary.dom s_dict).card (s_mid.mem (base + hdrSplit) + itemBatchWhp) →
          (splitPairRead cfg (s_mid.mem (base + hdrSplit)) s_mid.mem d).1 < 2 ^ cfg.qBitsLo ∧
          (splitPairRead cfg (s_mid.mem (base + hdrSplit)) s_mid.mem d).2 < 2 ^ cfg.vBitsLo :=
        fun d hd_lo hd_hi => by
          have hd_lt : d < (Dictionary.dom s_dict).card := lt_of_lt_of_le hd_hi (min_le_left _ _)
          have hq_b := hhi_quot d hd_lo hd_lt
          have hv_b : (slotIoPairAt io_sp s_mid.mem d).2 < V :=
            (hsl_d0.slot_pair_bounds (hns_d.symm ▸ hd_lt)).2
          have hv_pow : V ≤ 2 ^ valBits V := Nat.le_pow_clog (by decide : 1 < 2) V
          unfold slotIoPairAt at hv_b
          dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg] at hv_b
          simp only [↓reduceIte, one_ne_zero] at hv_b
          change (splitPairRead cfg (s_mid.mem (base + hdrSplit)) s_mid.mem d).2 < V at hv_b
          unfold splitPairRead at hv_b ⊢
          rw [ite_eq_right (Nat.not_lt.mpr hd_lo)] at hv_b ⊢
          exact ⟨hq_b, lt_of_lt_of_le hv_b hv_pow⟩
      obtain ⟨_, _, _, _, _, hout_sb⟩ := slideDownBatchProg_spec (cfg := cfg)
        (n_tot := (Dictionary.dom s_dict).card) (s_split := s_mid.mem (base + hdrSplit))
        (s := s_mid) hcfg_v hsp_le itemBatchWhp hfit
      have hibLo_192 : base + 192 ≤ cfg.baseLo := by dsimp only [cfg]; rw [hibLo_e]; omega
      rw [hctx, hmid.live_eq]
      split_ifs
      · refine Or.inr ⟨by dsimp only; rw [Function.update_self]; decide, ?_⟩
        dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + hdrNDst)
            (by dsimp only [hdrPBase0, hdrNDst]; omega)]
        dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          hout_sb (base + hdrNDst) (by dsimp only [hdrNDst]; omega)]
      · refine Or.inr ⟨?_, ?_⟩
        · dsimp only
          rw [Function.update_of_ne (base_add_ne (by decide)),
            hout_sb (base + hdrPhase) (by dsimp only [hdrPhase]; omega), hp_val]
          decide
        · dsimp only
          rw [Function.update_of_ne (base_add_ne (by decide)),
            hout_sb (base + hdrNDst) (by dsimp only [hdrNDst]; omega)]
    · simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      rw [hbgev]; exact Or.inr ⟨by rw [hp_val]; decide, rfl⟩
  have hw_t := dualPreShrinkInv_hdr_w hpre
  have hnot_rf : ¬(s_tick.mem (base + hdrPhase) = 5 ∧
      s_tick.mem ((if s_tick.mem (base + hdrStage) = 0 then base + hdrPBase1
        else base + hdrPBase0) + 31) ≤ s_tick.mem (base + hdrCur)) := by
    rintro ⟨hp5, _⟩
    rcases htick_cls with ⟨_, h4⟩ | ⟨h9, _⟩ <;> omega
  have hs_ps_eval : s_ps =
      (Memory.spec 0).clientState s_tick (calcPostShrinkProg (base, s_tick.frontier)) := by
    dsimp only [s_ps]
    rw [(postRandShrinkProg_eval base s_tick.frontier opTag s_tick).1]
    dsimp only; rw [ite_eq_right hop_nz, ite_eq_right hnot_rf]
  have hcps := (calcPostShrinkProg_eval (curFr := s_tick.frontier) (hw_t ▸ hw_pos)).1
  dsimp only at hcps
  have hb192 : base + 192 ≤ s_tick.frontier - k_sh := hinv_post.base_fr
  have hmem_low : ∀ off < 48, s_post.mem (base + off) = s_ps.mem (base + off) :=
    fun off hoff => by
      dsimp only [s_post]
      rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
  rcases htick_cls with ⟨hp9_m, hp4_t⟩ | ⟨hp9_t, hnD_t⟩
  · have hnp2 : ¬p2 := fun ⟨h11, _⟩ => by omega
    have hs_ps_t : s_ps = s_tick := by
      rw [hs_ps_eval, hcps,
        ite_eq_right (fun ⟨h11, _⟩ => by dsimp only [s_tick] at hp4_t h11; omega)]
    exact Or.inl ⟨⟨hp9_m, hp4_t⟩, hnp2, (hmem_low hdrPhase (by decide)).trans (hs_ps_t ▸ hp4_t)⟩
  · have hnp1 : ¬p1 := fun ⟨_, h4⟩ => by omega
    by_cases hc11 : s_tick.mem (base + hdrPhase) = 11 ∧
        s_tick.frontier - (s_tick.mem (base + hdrItemLo) +
          pairStreamWords (s_tick.mem (base + hdrLive)) (s_tick.mem (base + hdrQLo))
            (s_tick.mem (base + hdrValBits)) (s_tick.mem (base + hdrW))) ≤ bulkBatchWhp
    · have hs_ps_fin : s_ps = (Memory.spec 0).clientState s_tick (finishShrinkPostProg base) := by
        rw [hs_ps_eval, hcps, ite_eq_left hc11]
      have hps0 : s_ps.mem (base + hdrPhase) = 0 := by
        rw [hs_ps_fin, (finishShrinkPostProg_eval base s_tick).1]; dsimp only
        rw [Function.update_self]
      exact Or.inr (Or.inl ⟨hnp1, ⟨hc11.1, hps0⟩, (hmem_low hdrPhase (by decide)).trans hps0⟩)
    · have hs_ps_t : s_ps = s_tick := by rw [hs_ps_eval, hcps, ite_eq_right hc11]
      have hnp2 : ¬p2 := by
        rintro ⟨_, h0⟩; rw [hs_ps_t] at h0
        dsimp only [s_tick] at hp9_t h0; omega
      exact Or.inr (Or.inr ⟨hnp1, hnp2,
        by rw [hmem_low hdrPhase (by decide), hs_ps_t]; exact hp9_t,
        (hmem_low hdrNDst (by decide)).trans (hs_ps_t ▸ hnD_t)⟩)

/-- Unified single-state `opCodeWhp` deterministic mutation lifter outside phases `{5, 8}`
(`ph ≤ 4`, `ph ∈ {6, 7}`, and `9 ≤ ph`). -/
theorem opCodeWhp_mutate_non58_exec {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {x : RData rWhp}
    (hrep : DualRep c U V w base s_dict L x)
    (o : Dynamic.Op U) (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hne5 : x.mem (base + hdrPhase) ≠ 5)
    (hne8 : x.mem (base + hdrPhase) ≠ 8) :
    let s := rMemState x
    let ph := x.mem (base + hdrPhase)
    let L_mid := L.applyFG ph opTag u v
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
    let s_tick := (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
    let k_sh := (Memory.spec 0).clientResult s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_ps := (Memory.spec 0).clientState s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_post : Memory.State :=
      { mem := clear s_ps.mem (s_tick.frontier - k_sh) k_sh, frontier := s_tick.frontier - k_sh }
    let s_dict' := ((Dynamic.spec U V U).stepFn s_dict o).1
    ∃ (y : RData rWhp) (T : ℕ) (L' L_post : DualLatent c U V),
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode o x)
        (PMF.pure ⟨y, T, true⟩) (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      rMemState y = s_post ∧
      DualRep c U V w base s_dict' L_post y ∧
      DualMidInv c U V w base s_dict' L_mid s_mid ∧
      s_mid.mem (base + hdrPhase) = ph ∧
      s_tick = (Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)) ∧
      DualPreShrinkInv c U V w base s_dict' L' s_tick ∧
      PreservesEpochSeeds False (ph = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L_mid L' ∧
      PreservesEpochSeeds False
        (s_tick.mem (base + hdrPhase) = 11 ∧ s_ps.mem (base + hdrPhase) = 0) L' L_post ∧
      whpDecode (V := V) o y.regs = some ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
        (9 ≤ ph → L_mid.slotDst.GoodCovers) →
        T ≤ worstCaseTimeWhp c) := by
  intro s ph L_mid k_grow s_prep s_grow s_mid s_tick k_sh s_ps s_post s_dict'
  obtain ⟨y, T, hex, hy_mem, hyb, hy_base, hy_mfr, hy_dec, hy_out, hT_imp⟩ :=
    opCodeWhp_mutate_det_exec hrep o hv hfit_peak u v ho_mut hne5
  have hinv := hrep.2.2.2
  have hop_nz : opTag ≠ 0 := by rcases ho_mut with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
  have hv_eq : opTag = 1 → v_val = v.val := by
    rcases ho_mut with ⟨_, _, hv_v⟩ | ⟨_, rfl, _⟩
    · exact fun _ => hv_v
    · intro h; cases h
  have hs_dict'_eq :
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) = s_dict' := by
    rcases ho_mut with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  obtain ⟨_, hpad'_le⟩ := dualPaddedWords_step_le_peak hinv hop_nz u v
  have hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w := by
    rw [hs_dict'_eq]
    exact lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) base) hfit_peak
  have hpad_fits' :
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst))
        (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
          else Function.update s_dict u none)).card < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left hpad'_le base) hsucc_fits'
  obtain ⟨_, _, _, hmc_pg, _, _, _, _, _, _, hmid0, hpt_inv, hmc_so_eq, hmc_um⟩ :=
    stepOpProg_mutate_spec hinv hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hmid : DualMidInv c U V w base s_dict' L_mid s_mid := hs_dict'_eq ▸ hmid0
  have hsetup := fgSetup_of_dualStateInv hinv hop_nz u v
  have hsm_ph : s_mid.mem (base + hdrPhase) = ph := by
    by_cases hle7 : ph ≤ 7
    · exact (fgStep_le7_aux hinv u v hv_eq hsetup rfl rfl rfl hle7).2.2.2.1
        (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    · exact (fgStep_ge9_aux hinv u v hv_eq hsetup rfl rfl rfl
        (show 9 ≤ s.mem (base + hdrPhase) by change 9 ≤ ph; omega)).2.2.2.1
        (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
  have hfr_mid : s_mid.frontier = s_grow.frontier :=
    (prepGrow_userMutate_spec hinv hop_nz u v hv_eq hpad_fits').2.2.2.2.2.2.2.1
  have htick_eq : s_tick =
      (Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)) := by
    dsimp only [s_tick]
    rw [(stepOpProg_eval base s_grow.frontier opTag u.val v_val s_grow).1,
      ite_eq_right hop_nz, hfr_mid]
  obtain ⟨_, _, _, hpt_br⟩ := hpt_inv
  rw [ite_eq_left (hsm_ph.symm ▸ hne5)] at hpt_br
  obtain ⟨_, L', hpres1, hpre_sh0, hmc_bg0⟩ := hpt_br
  have hpre_sh : DualPreShrinkInv c U V w base s_dict' L' s_tick := hs_dict'_eq ▸ hpre_sh0
  have hpres1' : PreservesEpochSeeds False
      (ph = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L_mid L' := by
    rw [hsm_ph] at hpres1
    have h8f : (ph = 8) = False := eq_false hne8
    rw [h8f] at hpres1
    exact hpres1
  have hmc_bg : memoryCost (bgTickProg (base, s_mid.frontier)) s_mid ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 :=
    hmc_bg0 (fun h8 => absurd (hsm_ph.symm.trans h8) hne8)
      (fun h8 => absurd (hsm_ph.symm.trans h8) hne8)
  obtain ⟨_, _, _, _, _, hmc_prs, L_post, hpres2, hinv_post⟩ :=
    postRandShrinkProg_spec_pre hop_nz hpre_sh
  refine ⟨y, T, L', L_post, hex, hy_mem, ⟨hyb, hy_base, hy_mfr, hy_mem.symm ▸ hinv_post⟩,
    hmid, hsm_ph, htick_eq, hpre_sh, hpres1', hpres2, hy_dec, hy_out, fun hg7 hg9 => ?_⟩
  have hmc_pg' : memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 := hmc_pg
  have hmc_prs' : memoryCost (postRandShrinkProg ((base, s_tick.frontier), opTag)) s_tick ≤
      115 := by
    have hp6 : memoryCost (postRandShrinkProg ((base, s_tick.frontier), opTag)) s_tick ≤ 35 :=
      hmc_prs
    omega
  have hc_um : memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
      2 * epochStepCost c + 80 :=
    hmc_um hg7 (fun h8 => absurd h8 hne8) hg9
  have hmc_so' : memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow ≤
      (2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) := by
    have heq : memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow =
        memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow +
          memoryCost (bgTickProg (base, s_mid.frontier)) s_mid := hmc_so_eq
    omega
  exact hT_imp hmc_pg' hmc_so' hmc_prs'

theorem ph5StateAt_cast {c w base k₁ k₂ : ℕ} {s_anc s : Memory.State}
    {ws₁ : Fin k₁ → Fin (2 ^ w)} {ws₂ : Fin k₂ → Fin (2 ^ w)}
    (hk : k₁ = k₂) (hws : ∀ i : Fin k₂, ws₁ (i.cast hk.symm) = ws₂ i)
    (h : Ph5StateAt c w base s_anc k₁ ws₁ s) :
    Ph5StateAt c w base s_anc k₂ ws₂ s := by
  subst hk
  have heq : ws₁ = ws₂ := funext hws
  subst heq
  exact h

theorem finishRandFill_hdr_eq {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {st : Memory.State}
    (hm : DualMidInv c U V w base s_dict L st)
    (hp5 : st.mem (base + hdrPhase) = 5)
    (hpre_rf : FinishRandFillPre w base st)
    {k : ℕ} (hk : k < 48) (hne_ph : k ≠ hdrPhase) (hne_cur : k ≠ hdrCur) :
    ((Memory.spec 0).clientState st (finishRandFillProg base)).mem (base + k) =
      st.mem (base + k) := by
  rw [(finishRandFillProg_eval base st).1]; dsimp only
  rw [Function.update_of_ne (base_add_ne hne_ph), Function.update_of_ne (base_add_ne hne_cur)]
  obtain ⟨hd_pos, _, _, _, _, _⟩ := hm.ph5_inv hp5
  obtain ⟨_, _, _, _, _, _, hepre⟩ := hpre_rf
  set pD := if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
  set md := if st.mem (base + hdrStage) = 0 then base + 192 + st.mem (base + hdrPad)
    else base + 192
  set msk := ((1 : ℕ) <<< (st.mem (base + hdrRedW) - 1)) - 1
  set s1_st : Memory.State :=
    { mem := Function.update
        (Function.update st.mem (md + 32) (st.mem (md + 32) &&& msk))
        (md + st.mem (pD + 30)) (st.mem (md + st.mem (pD + 30)) &&& msk)
      frontier := st.frontier }
  set s2_st := (Memory.spec 0).clientState s1_st
    (setDirectSlotIoProg ((base, pD),
      ((st.mem (base + hdrItemHi), st.mem (base + hdrQHi)), st.mem (base + hdrLive))))
  change EpochProgPre w pD s2_st at hepre
  have hpD_d : pD = dualPDst base st.mem := by
    dsimp only [pD]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
  have hpD_0 : s2_st.mem pD = st.mem (base + hdrNDst) := by
    dsimp only [s2_st]
    rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
      (setSlotIoProg_frame pD _).mem_outside _ pD (by omega)]
    dsimp only [s1_st, md]
    rw [Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
      Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
      hpD_d]
    have h0 := (hm.ph5_inv hp5).2.2.2.1 0 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h0
    unfold dualPh5MaskMem at h0
    iterate 13 rw [Function.update_of_ne (by omega)] at h0
    simpa only [Nat.add_zero] using h0
  unfold EpochProgPre at hepre
  rcases hepre with ⟨hz, _⟩ | ⟨_, fl_st, hpB_e, hr_s2⟩
  · exact absurd (hpD_0.symm.trans hz) hd_pos.ne'
  · have hmconf := epochInitZeroedProg_meta_confine hr_s2
    have hmb_fl : fl_st.metaBase = md := by
      have h1 := hr_s2.2.1 1 (by decide)
      dsimp only [FastEpochLayout.paramWord, s2_st] at h1
      rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
        (setSlotIoProg_frame pD _).mem_outside _ (fl_st.pBase + 1)
          (by rw [hpB_e]; omega)] at h1
      dsimp only [s1_st, md] at h1 ⊢
      rw [hpB_e] at h1
      rw [Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
        Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
        hpD_d] at h1
      have h1' := (hm.ph5_inv hp5).2.2.2.1 1 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h1'
      unfold dualPh5MaskMem at h1'
      iterate 13 rw [Function.update_of_ne (by omega)] at h1'
      have hmb_d : dualMbDst base st.mem = md := by
        unfold dualMbDst; rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
      exact h1.symm.trans (h1'.trans hmb_d)
    have hmd_192 : base + 192 ≤ fl_st.metaBase := by
      rw [hmb_fl]; dsimp only [md]; split_ifs <;> omega
    rw [← hpB_e, hmconf (base + k) (by omega)]
    dsimp only [s2_st]
    rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
      (setSlotIoProg_frame pD _).mem_outside _ (base + k)
        (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
    dsimp only [s1_st, md]
    have hmd_lo : base + 192 ≤ md := by dsimp only [md]; split_ifs <;> omega
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem coupled67_symm {c w base : ℕ} {s₁ s₂ : Memory.State}
    (h : Coupled67 c w base s₁ s₂) : Coupled67 c w base s₂ s₁ := by
  obtain ⟨hsch, hreg⟩ := h
  have hcr : Coupled67Region c w base s₂.mem = Coupled67Region c w base s₁.mem := by
    funext addr
    unfold Coupled67Region dualMbDst dualPgHost dualNHost dualMbHost
    rw [hsch.2 hdrPhase (by decide) (by decide), hsch.2 hdrNDst (by decide) (by decide),
      hsch.2 hdrNSrc (by decide) (by decide), hsch.2 hdrStage (by decide) (by decide),
      hsch.2 hdrPad (by decide) (by decide), hsch.2 hdrItemHi (by decide) (by decide),
      hsch.2 hdrQHi (by decide) (by decide)]
  exact ⟨hsch.symm, fun addr ha => (hreg addr (hcr ▸ ha)).symm⟩

theorem coupled67_trans {c w base : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h12 : Coupled67 c w base s₁ s₂) (h23 : Coupled67 c w base s₂ s₃) :
    Coupled67 c w base s₁ s₃ := by
  obtain ⟨hsch12, hreg12⟩ := h12
  obtain ⟨hsch23, hreg23⟩ := h23
  have hcr12 : Coupled67Region c w base s₂.mem = Coupled67Region c w base s₁.mem := by
    funext addr
    unfold Coupled67Region dualMbDst dualPgHost dualNHost dualMbHost
    rw [hsch12.2 hdrPhase (by decide) (by decide), hsch12.2 hdrNDst (by decide) (by decide),
      hsch12.2 hdrNSrc (by decide) (by decide), hsch12.2 hdrStage (by decide) (by decide),
      hsch12.2 hdrPad (by decide) (by decide), hsch12.2 hdrItemHi (by decide) (by decide),
      hsch12.2 hdrQHi (by decide) (by decide)]
  exact ⟨hsch12.trans hsch23, fun addr ha =>
    (hreg12 addr ha).trans (hreg23 addr (hcr12.symm ▸ ha))⟩

/-- Preserves `hdrNDst` and bounds `s_tick.mem (base + hdrPhase) ≠ 11` across `bgTickProg` and
`postRandShrinkProg` starting from `s_mid.mem (base + hdrPhase) ∈ {6, 7}`. -/
theorem bgTick_post_from_67 {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L_mid L' L_post : DualLatent c U V} {s_mid : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hmid : DualMidInv c U V w base s_dict L_mid s_mid)
    (hp67 : s_mid.mem (base + hdrPhase) = 6 ∨ s_mid.mem (base + hdrPhase) = 7)
    (hpre : DualPreShrinkInv c U V w base s_dict L'
      ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))))
    (hinv_post : DualStateInv c U V w base s_dict L_post
      { mem := clear
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag))).mem
          (((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)))
          ((Memory.spec 0).clientResult
            ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
            (postRandShrinkProg ((base,
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
              opTag)))
        frontier :=
          ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier -
            (Memory.spec 0).clientResult
              ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier)))
              (postRandShrinkProg ((base,
                ((Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))).frontier),
                opTag)) }) :
    let s_tick := (Memory.spec 0).clientState s_mid (bgTickProg (base, s_mid.frontier))
    let s_ps := (Memory.spec 0).clientState s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_post : Memory.State :=
      { mem := clear s_ps.mem (s_tick.frontier - k_sh) k_sh, frontier := s_tick.frontier - k_sh }
    s_tick.mem (base + hdrPhase) ≠ 11 ∧
    s_post.mem (base + hdrNDst) = s_mid.mem (base + hdrNDst) := by
  intro s_tick s_ps k_sh s_post
  have hw_pos : 0 < w := by have := hmid.hw11; omega
  have htick_678 : (s_tick.mem (base + hdrPhase) = 6 ∨ s_tick.mem (base + hdrPhase) = 7 ∨
      s_tick.mem (base + hdrPhase) = 8) ∧
      s_tick.mem (base + hdrNDst) = s_mid.mem (base + hdrNDst) := by
    have hbgev := (bgTickProg_eval base s_mid.frontier s_mid).1
    dsimp only at hbgev; change s_tick = _ at hbgev
    rcases hp67 with hp6 | hp7
    · obtain ⟨_, _, _, _, _, hctx1, _, _, hv_m⟩ :=
        dualPgHost_eval_valid hmid (by rw [hp6]; decide) (by rw [hp6]; decide)
      have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := 0) hmid
        (by rw [hp6]; decide) (by rw [hp6]; decide)
      set nHost := dualNHost base s_mid.mem
      set mbHost := dualMbHost base s_mid.mem
      set pgM := hostPageLayout c w nHost mbHost (s_mid.mem (base + hdrItemHi)) 0 0 nHost
      have hdb_sp := pageInitDirBatchProg_spec (L := pgM) (cur := s_mid.mem (base + hdrCur))
        (s := s_mid) hv_m (hmid.ph6_inv hp6).1 bulkBatchWhp
      rw [hp6] at hbgev; simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      have htdev := (tickInitDirProg_eval base s_mid).1
      rw [hctx1, PageArenaLayout.ofCtx_toCtx, hmid.live_eq] at htdev
      rw [hbgev, htdev]
      by_cases hlt_mp : (Memory.spec 0).clientResult s_mid
          (pageInitDirBatchProg ((pgM.toCtx, s_mid.mem (base + hdrCur)), bulkBatchWhp)) <
          pgM.maxPages
      · rw [ite_eq_left hlt_mp]
        refine ⟨Or.inl ?_, ?_⟩ <;> dsimp only
        · rw [Function.update_of_ne (base_add_ne (by decide)),
            hdb_sp.2.2.2.2.1 _ (fun hd => by
              have := (hdisj_pg _ (Or.inr (Or.inl hd))).1; dsimp only [hdrPhase] at this; omega)]
          exact hp6
        · rw [Function.update_of_ne (base_add_ne (by decide)),
            hdb_sp.2.2.2.2.1 _ (fun hd => by
              have := (hdisj_pg _ (Or.inr (Or.inl hd))).1; dsimp only [hdrNDst] at this; omega)]
      · rw [ite_eq_right hlt_mp]
        refine ⟨Or.inr (Or.inl (Function.update_self ..)), ?_⟩; dsimp only
        iterate 4 rw [Function.update_of_ne (base_add_ne (by decide))]
        exact hdb_sp.2.2.2.2.1 _ (fun hd => by
          have := (hdisj_pg _ (Or.inr (Or.inl hd))).1; dsimp only [hdrNDst] at this; omega)
    · obtain ⟨_, _, _, _, hctx0, hctx1, _, _, hv_m⟩ :=
        dualPgHost_eval_valid hmid (by rw [hp7]; decide) (by rw [hp7]; decide)
      have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) hmid
        (by rw [hp7]; decide) (by rw [hp7]; decide)
      set nHost := dualNHost base s_mid.mem
      set mbHost := dualMbHost base s_mid.mem
      set pgM := hostPageLayout c w nHost mbHost (s_mid.mem (base + hdrItemHi)) 0 0 nHost
      obtain ⟨hns_h, _, _, ⟨_, _, hcur_lt8, _, _⟩, _⟩ := hmid.ph7_inv hp7
      have htb_sp := pageInitTailBatchProg_spec (L := pgM) (n_0 := s_mid.mem (base + hdrNSnap))
        (cur := s_mid.mem (base + hdrCur)) (s := s_mid) hv_m hns_h hcur_lt8.le tailBatchWhp
      rw [hp7] at hbgev; simp only [Nat.reduceEqDiff, ↓reduceIte] at hbgev
      have httev := (tickInitTailProg_eval base s_mid).1
      rw [hctx1, PageArenaLayout.ofCtx_toCtx] at httev
      set s2 := (Memory.spec 0).clientState s_mid (pageInitTailBatchProg
        (((pgM.toCtx, s_mid.mem (base + hdrNSnap)), s_mid.mem (base + hdrCur)), tailBatchWhp))
      have hs2_hdr : ∀ off < 192, s2.mem (base + off) = s_mid.mem (base + off) := fun off h192 =>
        htb_sp.2.2.2.2.1 (base + off) (fun ht => by
          have := (hdisj_pg _ (Or.inr (Or.inr ht))).1; clear *- h192 this; omega)
      rw [hbgev, httev]
      split_ifs with hlt8
      · refine ⟨Or.inr (Or.inl ?_), ?_⟩ <;> dsimp only
        · rw [Function.update_of_ne (base_add_ne (by decide))]
          exact (hs2_hdr _ (by decide)).trans hp7
        · rw [Function.update_of_ne (base_add_ne (by decide))]; exact hs2_hdr _ (by decide)
      · have hctx0_s2 : (Memory.spec 0).clientResult s2 (loadHostCtxProg (base, 0)) =
            (dualPgHost c V w base (Dictionary.dom s_dict).card s_mid.mem).toCtx := by
          rw [← hctx0, (loadHostCtxProg_eval base 0 s2).2.1,
            (loadHostCtxProg_eval base 0 s_mid).2.1]
          simp only [↓reduceIte]
          have h_od : ∀ k ≤ 4,
              s2.mem (base + (if s_mid.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
              s_mid.mem (base +
                (if s_mid.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
            fun k hk => by
              rw [Nat.add_assoc]
              exact hs2_hdr _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
          rw [hs2_hdr hdrStage (by decide), hs2_hdr hdrNDst (by decide),
            hs2_hdr hdrPad (by decide), hs2_hdr hdrW (by decide),
            hs2_hdr hdrItemHi (by decide), hs2_hdr hdrQHi (by decide),
            hs2_hdr hdrValBits (by decide), hs2_hdr hdrLive (by decide),
            show s2.mem (base + if s_mid.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
              s_mid.mem (base + if s_mid.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
              simpa only [Nat.add_zero] using h_od 0 (by decide),
            h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
        have hf_ev := (finishInitTailProg_eval base s2).1
        rw [hctx0_s2, PageArenaLayout.ofCtx_toCtx] at hf_ev
        rw [hf_ev]; dsimp only
        refine ⟨Or.inr (Or.inr (Function.update_self ..)), ?_⟩
        rw [Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide))]
        set pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s_mid.mem
        have hmb_ge192 : base + 192 ≤ pgH.metaBase := by
          change base + 192 ≤ dualMbHost base s_mid.mem; unfold dualMbHost; split_ifs <;> omega
        set pS := if s2.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1
        set pD := if s2.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
        have hpS_out : ¬(pS + 48 ≤ base + hdrNDst ∧ base + hdrNDst < pS + 61) := by
          dsimp only [pS, hdrPBase0, hdrPBase1, hdrNDst]; split_ifs <;> omega
        have hpD_out : ¬(pD + 48 ≤ base + hdrNDst ∧ base + hdrNDst < pD + 61) := by
          dsimp only [pD, hdrPBase0, hdrPBase1, hdrNDst]; split_ifs <;> omega
        have hpD_61 : ¬(pD ≤ base + hdrNDst ∧ base + hdrNDst < pD + 61) := by
          dsimp only [pD, hdrPBase0, hdrPBase1, hdrNDst]; split_ifs <;> omega
        by_cases hd0_s2 : s2.mem (base + hdrNDst) = 0
        · rw [ite_eq_left hd0_s2]
          let smL : SmallEpochLayout :=
            { U := U, V := V, metaBase := base + hdrSmallMeta1, io := pagedSlotIo 1 pgH }
          have hw_sm := (writeSmallParamTableProg_spec pD smL
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState s2
                (pageInitScalarsBandProg
                  ((pgH.metaBase, pgH.pgB),
                    (s2.mem (base + hdrQSnap),
                      s2.mem (base + hdrLive) - s2.mem (base + hdrQSnap) * pgH.pgB))))
              (setSlotIoProg (pS, (1, 0), pgH.toCtx)))).2.2.2
            (base + hdrNDst) hpD_61
          dsimp only [smL, pagedSlotIo, SlotIoLayout.toCtx] at hw_sm
          rw [hw_sm,
            (setSlotIoProg_frame _ _).mem_outside _ _ hpS_out,
            (pageInitScalarsBandProg_spec _ _ _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
              (by dsimp only [hdrNDst]; omega)]
          exact hs2_hdr _ (by decide)
        · rw [ite_eq_right hd0_s2,
            (setSlotIoProg_frame _ _).mem_outside _ _ hpD_out,
            (setSlotIoProg_frame _ _).mem_outside _ _ hpS_out,
            (pageInitScalarsBandProg_spec _ _ _ _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _
              (by dsimp only [hdrNDst]; omega)]
          exact hs2_hdr _ (by decide)
  have hne11 : s_tick.mem (base + hdrPhase) ≠ 11 := by
    rcases htick_678.1 with h | h | h <;> omega
  have hne5 : s_tick.mem (base + hdrPhase) ≠ 5 := by
    rcases htick_678.1 with h | h | h <;> omega
  have hw_t := dualPreShrinkInv_hdr_w hpre
  have hs_ps_eq : s_ps = s_tick := by
    dsimp only [s_ps]
    rw [(postRandShrinkProg_eval base s_tick.frontier opTag s_tick).1]; dsimp only
    rw [ite_eq_right hop_nz, ite_eq_right (fun h => hne5 h.1),
      (calcPostShrinkProg_eval (curFr := s_tick.frontier) (hw_t ▸ hw_pos)).1]; dsimp only
    rw [ite_eq_right (fun h => hne11 h.1)]
  have hb192 : base + 192 ≤ s_tick.frontier - k_sh := hinv_post.base_fr
  refine ⟨hne11, ?_⟩
  dsimp only [s_post]
  rw [hs_ps_eq, clear_of_not_owns (by simp only [Block.Owns]; dsimp only [hdrNDst]; omega)]
  exact htick_678.2

/-- Equivalence relation on Phase-`8` states sharing `Coupled8`, `slotSrc`, `slotDst.s_abs`, and
`slotDst.evs`, used to select a fibre-canonical anchor `rep8` depending only on `t`. -/
@[expose]
def Rel8 (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (t₁ t₂ : LatentRState (DualLatent c U V) rWhp) : Prop :=
  DualRep c U V w base s_dict t₁.latent t₁.data ∧
  DualRep c U V w base s_dict t₂.latent t₂.data ∧
  t₁.data.mem (base + hdrPhase) = 8 ∧
  Coupled8 c V w base (Dictionary.dom s_dict).card (rMemState t₁.data) (rMemState t₂.data) ∧
  t₂.latent.slotSrc = t₁.latent.slotSrc ∧
  t₂.latent.slotDst.s_abs = t₁.latent.slotDst.s_abs ∧
  t₂.latent.slotDst.evs = t₁.latent.slotDst.evs

theorem coupled8_symm {c V w base nLive : ℕ} {s₁ s₂ : Memory.State}
    (h : Coupled8 c V w base nLive s₁ s₂) : Coupled8 c V w base nLive s₂ s₁ := by
  obtain ⟨hsch, hc⟩ := h
  have hmb : dualMbSrc base s₂.mem = dualMbSrc base s₁.mem := hsch.mbSrc_eq.symm
  have hpg : dualPgHost c V w base nLive s₂.mem = dualPgHost c V w base nLive s₁.mem :=
    hsch.pgHost_eq.symm
  have hc8r : Coupled8Region c w base s₂.mem = Coupled8Region c w base s₁.mem := by
    funext addr
    unfold Coupled8Region dualPSrc dualMbSrc dualCapSrc
    rw [hsch.2 hdrStage (by decide) (by decide),
      hsch.2 hdrNSrc (by decide) (by decide),
      hsch.2 hdrNDst (by decide) (by decide),
      hsch.2 hdrPad (by decide) (by decide)]
  have hm1 : Coupled8Region c w base s₁.mem (dualMbSrc base s₁.mem + 1) := by
    unfold Coupled8Region SlotSrcMetaRegion slotOwnsNonPageMeta
    refine Or.inr (Or.inl ⟨Nat.le_add_right _ 1, ?_⟩)
    split_ifs <;> omega
  have hns : s₂.mem (dualMbSrc base s₂.mem + 1) = s₁.mem (dualMbSrc base s₁.mem + 1) := by
    rw [hmb]; exact (hc.mem_eq _ hm1).symm
  refine ⟨hsch.symm,
    { fr_eq := hc.fr_eq.symm
      side_zero := rfl
      valid₁ := by rw [hpg, ← hc.fr_eq]; exact hc.valid₁
      disj := fun addr hr ho => hc.disj addr (hc8r ▸ hr) (hpg ▸ ho)
      mem_eq := fun addr hr => (hc.mem_eq addr (hc8r ▸ hr)).symm
      inv₁ := by rw [hpg, hns]; exact hc.inv₂
      inv₂ := by rw [hpg, hns]; exact hc.inv₁
      pair_eq := fun idx hlt => by
        rw [hpg]; exact (hc.pair_eq idx (hns ▸ hlt)).symm }⟩

theorem coupled8_trans {c V w base nLive : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h12 : Coupled8 c V w base nLive s₁ s₂) (h23 : Coupled8 c V w base nLive s₂ s₃) :
    Coupled8 c V w base nLive s₁ s₃ := by
  obtain ⟨hsch12, hc12⟩ := h12
  obtain ⟨hsch23, hc23⟩ := h23
  have hmb12 : dualMbSrc base s₂.mem = dualMbSrc base s₁.mem := hsch12.mbSrc_eq.symm
  have hpg12 : dualPgHost c V w base nLive s₂.mem = dualPgHost c V w base nLive s₁.mem :=
    hsch12.pgHost_eq.symm
  have hc8r12 : Coupled8Region c w base s₂.mem = Coupled8Region c w base s₁.mem := by
    funext addr
    unfold Coupled8Region dualPSrc dualMbSrc dualCapSrc
    rw [hsch12.2 hdrStage (by decide) (by decide),
      hsch12.2 hdrNSrc (by decide) (by decide),
      hsch12.2 hdrNDst (by decide) (by decide),
      hsch12.2 hdrPad (by decide) (by decide)]
  have hm1 : Coupled8Region c w base s₁.mem (dualMbSrc base s₁.mem + 1) := by
    unfold Coupled8Region SlotSrcMetaRegion slotOwnsNonPageMeta
    refine Or.inr (Or.inl ⟨Nat.le_add_right _ 1, ?_⟩)
    split_ifs <;> omega
  have hns12 : s₂.mem (dualMbSrc base s₂.mem + 1) = s₁.mem (dualMbSrc base s₁.mem + 1) := by
    rw [hmb12]; exact (hc12.mem_eq _ hm1).symm
  refine ⟨hsch12.trans hsch23,
    { fr_eq := hc12.fr_eq.trans hc23.fr_eq
      side_zero := rfl
      valid₁ := hc12.valid₁
      disj := hc12.disj
      mem_eq := fun addr hr => (hc12.mem_eq addr hr).trans (hc23.mem_eq addr (hc8r12.symm ▸ hr))
      inv₁ := hc12.inv₁
      inv₂ := by have hi := hc23.inv₂; rwa [hpg12, hns12] at hi
      pair_eq := fun idx hlt => (hc12.pair_eq idx hlt).trans (by
        have hp := hc23.pair_eq idx (hns12.symm ▸ hlt)
        rwa [hpg12] at hp) }⟩

theorem Rel8.refl {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {t : LatentRState (DualLatent c U V) rWhp}
    (hr : DualRep c U V w base s_dict t.latent t.data)
    (hp8 : t.data.mem (base + hdrPhase) = 8) :
    Rel8 c U V w base s_dict t t :=
  ⟨hr, hr, hp8, Coupled8.refl hr.2.2.2 hp8, rfl, rfl, rfl⟩

theorem Rel8.symm {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {t₁ t₂ : LatentRState (DualLatent c U V) rWhp}
    (h : Rel8 c U V w base s_dict t₁ t₂) :
    Rel8 c U V w base s_dict t₂ t₁ :=
  ⟨h.2.1, h.1, (h.2.2.2.1.1.2 hdrPhase (by decide) (by decide)).symm.trans h.2.2.1,
   coupled8_symm h.2.2.2.1, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

theorem Rel8.trans {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {t₁ t₂ t₃ : LatentRState (DualLatent c U V) rWhp}
    (h12 : Rel8 c U V w base s_dict t₁ t₂) (h23 : Rel8 c U V w base s_dict t₂ t₃) :
    Rel8 c U V w base s_dict t₁ t₃ :=
  ⟨h12.1, h23.2.1, h12.2.2.1, coupled8_trans h12.2.2.2.1 h23.2.2.2.1,
   h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.trans h12.2.2.2.2.2.2⟩

private noncomputable def choosePred {α : Type} (dflt : α) (P : α → Prop) : α := by
  classical
  exact if h : ∃ r, P r then Classical.choose h else dflt

private theorem choosePred_spec {α : Type} (dflt : α) {P : α → Prop} (hex : ∃ r, P r) :
    P (choosePred dflt P) := by
  unfold choosePred
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

/-- Canonical `Rel8`-fibre anchor selected via `Classical.choose`, invariant across all
`slotDst.seeds` sharing the same `(slotSrc, slotDst.s_abs, slotDst.evs)` fibre. -/
noncomputable def rep8 (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (dflt : LatentRState (DualLatent c U V) rWhp)
    (t : LatentRState (DualLatent c U V) rWhp) : LatentRState (DualLatent c U V) rWhp :=
  choosePred dflt (fun r => Rel8 c U V w base s_dict r t)

theorem rep8_rel {c U V w base : ℕ} {s_dict : Dictionary.State U}
    (dflt : LatentRState (DualLatent c U V) rWhp)
    {t : LatentRState (DualLatent c U V) rWhp}
    (hr : DualRep c U V w base s_dict t.latent t.data)
    (hp8 : t.data.mem (base + hdrPhase) = 8) :
    Rel8 c U V w base s_dict (rep8 c U V w base s_dict dflt t) t :=
  choosePred_spec (P := fun r => Rel8 c U V w base s_dict r t) dflt ⟨t, Rel8.refl hr hp8⟩

theorem rep8_eq_of_rel {c U V w base : ℕ} {s_dict : Dictionary.State U}
    (dflt : LatentRState (DualLatent c U V) rWhp)
    {t₁ t₂ : LatentRState (DualLatent c U V) rWhp}
    (h : Rel8 c U V w base s_dict t₁ t₂) :
    rep8 c U V w base s_dict dflt t₁ = rep8 c U V w base s_dict dflt t₂ := by
  unfold rep8
  refine congrArg (choosePred dflt) (funext fun r => propext ⟨fun hr => ?_, fun hr => ?_⟩)
  · exact hr.trans h
  · exact hr.trans h.symm

/-! ## Section 3: Initialization and Query Preservation of `DualDistInv` -/

/-- `initCodeWhp` establishes `DualDistInv` at `Dictionary.empty U`. -/
theorem dualDistInv_init {c U V w base : ℕ} {x₀ : RData rWhp}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + spaceBoundWhp c V w (Dictionary.empty U))) :
    ∃ ν₀ : PMF (LatentRState (DualLatent c U V) rWhp),
      ExecRCodeSteps w (initCodeWhp c U V w) x₀
        (ν₀.map fun t => ⟨t.data, initStepsWhp, true⟩)
        (base + spaceBoundWhp c V w (Dictionary.empty U)) ∧
      DualDistInv c U V w base (Dictionary.empty U) ν₀ ∧
      ∀ t ∈ ν₀.support,
        DualRep c U V w base (Dictionary.empty U) t.latent t.data ∧
        (∀ addr < base, t.data.mem addr = x₀.mem addr) := by
  obtain ⟨y, hex, hrep, hbel⟩ := initCodeWhp_demonicExec hw11 hU0 hUw hV0 hVw hx₀ hfr₀ hfit₀
  let t₀ : LatentRState (DualLatent c U V) rWhp := ⟨DualLatent.empty c U V, y⟩
  have hex_steps : ExecRCodeSteps w (initCodeWhp c U V w) x₀
      ((PMF.pure t₀).map fun t => ⟨t.data, initStepsWhp, true⟩)
      (base + spaceBoundWhp c V w (Dictionary.empty U)) := by
    rw [PMF.pure_map]
    exact ExecRCodeSteps.of_demonicExec hex
  have hinv_y := hrep.2.2.2
  have hph_le4 : (rMemState y).mem (base + hdrPhase) ≤ 4 := by
    by_cases hp0 : (rMemState y).mem (base + hdrPhase) = 0
    · rw [hp0]; decide
    · exfalso
      have hsched := hinv_y.sched; rw [ite_eq_right hp0] at hsched
      have htrig := hsched.trig_cap
      have hpost := hsched.post_trig
      dsimp only [DualLatent.empty] at htrig hpost
      by_cases hs0 : y.mem (base + hdrNSrc) = 0
      · rw [hs0] at htrig
        unfold dualTriggerCap at htrig; simp only [↓reduceIte] at htrig
        have := whpThreshold_pos c
        rw [ite_eq_right (fun hk => by omega)] at htrig
        cases htrig
      · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost
        have := whpThreshold_ge_64 c
        omega
  have hcap0 : dualCapSrc base (rMemState y).mem = 0 := by
    have hc := (hinv_y.sl_le7 (by omega)).1
    exact hc.symm
  refine ⟨PMF.pure t₀, hex_steps, ⟨DualLatent.empty c U V, rMemState y, hinv_y, ?_⟩,
    fun t ht => ?_⟩
  · dsimp only
    rw [ite_eq_left hph_le4, hcap0]
    exact singleEpochLaw_zero fun t ht => by
      rw [PMF.mem_support_pure_iff] at ht; subst ht
      exact ⟨hrep, SchedEq.refl base _, rfl⟩
  · rw [PMF.mem_support_pure_iff] at ht; subst ht
    exact ⟨hrep, hbel⟩

/-- Read-only `query u` preserves `DualDistInv` and bounds slow-path probability by
`stepFailureProbWhp c s_dict (.query u)`. -/
theorem dualDistInv_step_query {c U V w base : ℕ}
    (s_dict : Dictionary.State U) (u : Fin U)
    (ν : PMF (LatentRState (DualLatent c U V) rWhp))
    (_hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict (.query u)))
    (hd : DualDistInv c U V w base s_dict ν)
    (hsupp : ∀ t ∈ ν.support, DualRep c U V w base s_dict t.latent t.data) :
    ∃ μ_step : LatentRState (DualLatent c U V) rWhp →
        PMF (WhpStepROutcome (DualLatent c U V) (Option ℕ) rWhp),
      (∀ t ∈ ν.support,
        ExecRCodeSteps w opCodeWhp
          ((subroutineCodeWhp c U V w).prepare whpEncode (.query u) t.data)
          ((μ_step t).map WhpStepROutcome.toCodeOutcome)
          (base + stepSuccinctPeakWordsWhp c V w s_dict (.query u)) ∧
        ∀ q ∈ (μ_step t).support,
          q.result = ((Dynamic.spec U V U).stepFn s_dict (.query u)).2 ∧
          whpDecode (V := V) (.query u) q.data.regs = some q.result ∧
          DualRep c U V w base ((Dynamic.spec U V U).stepFn s_dict (.query u)).1
            q.latent q.data ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      DualDistInv c U V w base ((Dynamic.spec U V U).stepFn s_dict (.query u)).1
        (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) ∧
      (ν.bind μ_step).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
        stepFailureProbWhp c s_dict (.query u) := by
  classical
  let L_peak := base + stepSuccinctPeakWordsWhp c V w s_dict (.query u)
  have hL_of_rep : ∀ {L x}, DualRep c U V w base s_dict L x → x.frontier ≤ L_peak := fun hr =>
    hr.frontier_le.2.1.trans (Nat.add_le_add_left (le_max_left _ _) base)
  let q_of : LatentRState (DualLatent c U V) rWhp →
      WhpStepROutcome (DualLatent c U V) (Option ℕ) rWhp := fun t =>
    if hr : DualRep c U V w base s_dict t.latent t.data then
      let hq := opCodeWhp_query_exec hr u (hL_of_rep hr)
      ⟨t.latent, hq.choose, s_dict u, hq.choose_spec.choose, true⟩
    else
      ⟨t.latent, t.data, s_dict u, 0, true⟩
  let μ_step := fun t => PMF.pure (q_of t)
  have hq_spec : ∀ {t : LatentRState (DualLatent c U V) rWhp}
      (hr : DualRep c U V w base s_dict t.latent t.data),
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode (.query u) t.data)
        (PMF.pure ⟨(q_of t).data, (q_of t).steps, true⟩) L_peak ∧
      rMemState (q_of t).data = rMemState t.data ∧
      DualRep c U V w base s_dict t.latent (q_of t).data ∧
      whpDecode (V := V) (.query u) (q_of t).data.regs = some (s_dict u) ∧
      (∀ addr < base, (q_of t).data.mem addr = t.data.mem addr) ∧
      (t.latent.ActiveGood (t.data.mem (base + hdrPhase)) →
        (q_of t).steps ≤ worstCaseTimeWhp c) := fun {t} hr => by
    dsimp only [q_of]
    rw [dite_eq_left hr]
    exact (opCodeWhp_query_exec hr u (hL_of_rep hr)).choose_spec.choose_spec
  have hstep_supp : ∀ t ∈ ν.support,
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode (.query u) t.data)
        ((μ_step t).map WhpStepROutcome.toCodeOutcome) L_peak ∧
      ∀ q ∈ (μ_step t).support,
        q.result = s_dict u ∧
        whpDecode (V := V) (.query u) q.data.regs = some q.result ∧
        DualRep c U V w base s_dict q.latent q.data ∧
        (∀ addr < base, q.data.mem addr = t.data.mem addr) := by
    intro t ht
    have hr := hsupp t ht
    obtain ⟨hex, _, hrep', hdec, hout, _⟩ := hq_spec hr
    refine ⟨?_, fun q hq => ?_⟩
    · dsimp only [μ_step, q_of]; rw [dite_eq_left hr, PMF.pure_map]
      dsimp only [q_of] at hex; rw [dite_eq_left hr] at hex
      exact hex
    · rw [PMF.mem_support_pure_iff] at hq; subst hq
      have hlat : (q_of t).latent = t.latent := by dsimp only [q_of]; rw [dite_eq_left hr]
      have hres : (q_of t).result = s_dict u := by dsimp only [q_of]; rw [dite_eq_left hr]
      exact ⟨hres, hres ▸ hdec, hlat ▸ hrep', hout⟩
  let adv : LatentRState (DualLatent c U V) rWhp → LatentRState (DualLatent c U V) rWhp :=
    fun t => ⟨t.latent, (q_of t).data⟩
  have hν'_eq : (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) = ν.map adv := by
    dsimp only [μ_step]
    conv_rhs => unfold PMF.map
    refine congrArg (ν.bind ·) (funext fun t => ?_)
    dsimp only [Function.comp_def]
    rw [PMF.pure_map]
    have hlat : (q_of t).latent = t.latent := by
      dsimp only [q_of]; split_ifs <;> rfl
    rw [hlat]
  obtain ⟨L_rep, s_rep, hinv_rep, hregimes⟩ := hd
  have hUw : Fits w U := hinv_rep.U_lt
  set ph := s_rep.mem (base + hdrPhase)
  set capSrc := dualCapSrc base s_rep.mem
  set capDst := s_rep.mem (base + hdrNDst)
  have hsrc_safe := dualCapSrc_safe hinv_rep
  refine ⟨μ_step, hstep_supp, ?_, ?_⟩
  · -- Preserve `DualDistInv` under `ν.map adv` (`rMemState (adv t).data = rMemState t.data`)
    rw [hν'_eq]
    change DualDistInv c U V w base s_dict (ν.map adv)
    refine ⟨L_rep, s_rep, hinv_rep, ?_⟩
    dsimp only
    by_cases hp4 : ph ≤ 4
    · rw [ite_eq_left hp4] at hregimes ⊢
      obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
      refine ⟨α, μ_idx, evs_of, fun a ws => adv (f_act a ws), ?_, fun a ha ws => ?_⟩
      · rw [hν, PMF.map_bind]; simp only [PMF.map_comp, Function.comp_def]; rfl
      · obtain ⟨hr, hsch, hnc, hev, hsd⟩ := hf a ha ws
        obtain ⟨_, hmem_eq, hr', _, _, _⟩ := hq_spec hr
        exact ⟨hr', hmem_eq.symm ▸ hsch, hnc, hev, hsd⟩
    · rw [ite_eq_right hp4] at hregimes ⊢
      by_cases hp5 : ph = 5
      · rw [ite_eq_left hp5] at hregimes ⊢
        obtain ⟨α, μ_idx, k_pre, evs_src, L_anc, s_anc, f5, hν, hf⟩ := hregimes
        refine ⟨α, μ_idx, k_pre, evs_src, L_anc, s_anc, fun a ws wp => adv (f5 a ws wp), ?_,
          fun a ha ws => ?_⟩
        · rw [hν, PMF.map_bind]
          refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
          rw [PMF.map_bind]; simp only [PMF.map_comp, Function.comp_def]; rfl
        · obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, hwp⟩ := hf a ha ws
          refine ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, fun wp => ?_⟩
          obtain ⟨hr, hph5, hsl⟩ := hwp wp
          obtain ⟨_, hmem_eq, hr', _, _, _⟩ := hq_spec hr
          exact ⟨hr', hmem_eq.symm ▸ hph5, hsl⟩
      · rw [ite_eq_right hp5] at hregimes ⊢
        by_cases hp67 : ph = 6 ∨ ph = 7
        · rw [ite_eq_left hp67] at hregimes ⊢
          obtain ⟨α, μ_idx, evs_src, L_anc, s_anc, f67, hν, hf⟩ := hregimes
          refine ⟨α, μ_idx, evs_src, L_anc, s_anc, fun a ws wd => adv (f67 a ws wd), ?_,
            fun a ha ws => ?_⟩
          · rw [hν, PMF.map_bind]
            refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
            rw [PMF.map_bind]; simp only [PMF.map_comp, Function.comp_def]; rfl
          · obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, hwd⟩ := hf a ha ws
            refine ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, fun wd => ?_⟩
            obtain ⟨hr, hc67, hsl, hdst⟩ := hwd wd
            obtain ⟨_, hmem_eq, hr', _, _, _⟩ := hq_spec hr
            exact ⟨hr', hmem_eq.symm ▸ hc67, hsl, hdst⟩
        · rw [ite_eq_right hp67] at hregimes ⊢
          by_cases hp8 : ph = 8
          · rw [ite_eq_left hp8] at hregimes ⊢
            obtain ⟨α, μ_idx, evs_src, evs_dst, L_anc, s_anc, f8, hν, hf⟩ := hregimes
            refine ⟨α, μ_idx, evs_src, evs_dst, L_anc, s_anc,
              fun a ws wd => adv (f8 a ws wd), ?_, fun a ha ws => ?_⟩
            · rw [hν, PMF.map_bind]
              refine congrArg (μ_idx.bind ·) (funext fun a => ?_)
              rw [PMF.map_bind]; simp only [PMF.map_comp, Function.comp_def]; rfl
            · obtain ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, ha_de, hwd⟩ := hf a ha ws
              refine ⟨ha_inv, ha_sch, ha_nc, ha_ev, ha_sd, ha_de, fun wd => ?_⟩
              obtain ⟨hr, hc8, hsl, hdn, hda, hde, hds⟩ := hwd wd
              obtain ⟨_, hmem_eq, hr', _, _, _⟩ := hq_spec hr
              exact ⟨hr', hmem_eq.symm ▸ hc8, hsl, hdn, hda, hde, hds⟩
          · rw [ite_eq_right hp8] at hregimes ⊢
            obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
            refine ⟨α, μ_idx, evs_of, fun a ws => adv (f_act a ws), ?_, fun a ha ws => ?_⟩
            · rw [hν, PMF.map_bind]; simp only [PMF.map_comp, Function.comp_def]; rfl
            · obtain ⟨hr, hsch, hnc, hev, hsd⟩ := hf a ha ws
              obtain ⟨_, hmem_eq, hr', _, _, _⟩ := hq_spec hr
              exact ⟨hr', hmem_eq.symm ▸ hsch, hnc, hev, hsd⟩
  · -- Failure probability bound across all 5 regimes
    by_cases hp4 : ph ≤ 4
    · rw [ite_eq_left hp4] at hregimes
      obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
      rw [hν, PMF.bind_bind]
      refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
      rw [PMF.bind_map]
      refine (toOuterMeasure_map_pure_le _ _ _
        (fun ws => (f_act a ws).latent.slotSrc.GoodCovers) fun ws hgc hbad => ?_).trans ?_
      · obtain ⟨hr, hsch, _, _, _⟩ := hf a ha ws
        obtain ⟨_, _, _, _, _, hT⟩ := hq_spec hr
        have hph_t : (f_act a ws).data.mem (base + hdrPhase) = ph :=
          (hsch.2 hdrPhase (by decide) (by decide)).symm
        have hag : (f_act a ws).latent.ActiveGood ((f_act a ws).data.mem (base + hdrPhase)) := by
          unfold DualLatent.ActiveGood
          rw [hph_t]; exact ⟨fun _ => hgc, fun h8 => absurd (h8.trans hp4) (by decide)⟩
        have htimed : (q_of (f_act a ws)).timed = true := by dsimp only [q_of]; rw [dite_eq_left hr]
        exact hbad ⟨htimed, hT hag⟩
      · refine (uniform_seedWords_bad_le hUw hsrc_safe (evs_of a)
          (fun ws => (f_act a ws).latent.slotSrc)
          (fun ws => (hf a ha ws).2.2.1) (fun ws => (hf a ha ws).2.2.2.1)
          (fun hc ws => (hf a ha ws).2.2.2.2 hc) fun hc => ?_).trans
          (half_stepFailureProb_le c s_dict (.query u))
        let ws₀ := zeroSeedWords c w capSrc
        obtain ⟨hr₀, hsch₀, hnc₀, hev₀, _⟩ := hf a ha ws₀
        change (f_act a ws₀).latent.slotSrc.nCap = _ at hnc₀
        change (f_act a ws₀).latent.slotSrc.evs = _ at hev₀
        have hb₀ := (dualCoreInv_slot_evs_bounds hr₀.2.2.2).1
          (by rw [(hsch₀.2 hdrPhase (by decide) (by decide)).symm]; change ph ≤ 8; omega)
          (hnc₀ ▸ hc)
        rwa [hnc₀, hev₀] at hb₀
    · rw [ite_eq_right hp4] at hregimes
      by_cases hp5 : ph = 5
      · rw [ite_eq_left hp5] at hregimes
        obtain ⟨α, μ_idx, k_pre, evs_src, L_anc, s_anc, f5, hν, hf⟩ := hregimes
        rw [hν, PMF.bind_bind]
        refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
        rw [PMF.bind_bind]
        let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
        let B_half := if U < whpThreshold c then (0 : ℝ≥0∞)
          else ((1 : ℝ≥0∞) / 2) *
            (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)
        have h_inner : ∀ ws_src : SeedWords c w capSrc,
            (((PMF.uniformOfFintype (Fin k_pre → Fin (2 ^ w))).map (f5 a ws_src)).bind μ_step
              ).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
            if (L_anc a ws_src).slotSrc.GoodCovers then 0 else 1 := fun ws_src => by
          obtain ⟨_, ha_sch, _, _, _, hwp⟩ := hf a ha ws_src
          by_cases hgc : (L_anc a ws_src).slotSrc.GoodCovers
          · rw [ite_eq_left hgc]
            refine toOuterMeasure_bind_le_const _ _ _ 0 fun t ht => ?_
            rw [PMF.mem_support_map_iff] at ht; obtain ⟨wp, _, rfl⟩ := ht
            obtain ⟨hr, hph5, hsl⟩ := hwp wp
            have hsch_t := ha_sch.trans (hph5.schedEq (hf a ha ws_src).1)
            have hph_t : (f5 a ws_src wp).data.mem (base + hdrPhase) = 5 :=
              (hsch_t.2 hdrPhase (by decide) (by decide)).symm.trans hp5
            obtain ⟨_, _, _, _, _, hT⟩ := hq_spec hr
            have hag : (f5 a ws_src wp).latent.ActiveGood
                ((f5 a ws_src wp).data.mem (base + hdrPhase)) := by
              unfold DualLatent.ActiveGood
              rw [hph_t, hsl]; exact ⟨fun _ => hgc, fun h8 => absurd h8 (by decide)⟩
            have htimed : (q_of (f5 a ws_src wp)).timed = true := by
              dsimp only [q_of]; rw [dite_eq_left hr]
            rw [PMF.toOuterMeasure_apply]
            refine (tsum_eq_zero_iff.mpr fun q => ?_).le
            by_cases hq_eq : q = q_of (f5 a ws_src wp)
            · subst hq_eq
              have hnot : q_of (f5 a ws_src wp) ∉
                  {q | ¬q.WithinBudget (worstCaseTimeWhp c)} := fun hnb =>
                hnb ⟨htimed, hT hag⟩
              simp [hnot]
            · simp [μ_step, PMF.pure_apply, hq_eq]
          · rw [ite_eq_right hgc]; exact PMF.toOuterMeasure_le_one _ _
        calc (μ_src.bind _).toOuterMeasure _
            = ∑' ws_src, μ_src ws_src * _ := PMF.toOuterMeasure_bind_apply _ _ _
          _ ≤ ∑' ws_src, μ_src ws_src *
                (if (L_anc a ws_src).slotSrc.GoodCovers then 0 else 1) :=
              tsum_le_tsum fun ws_src => mul_le_mul_right (h_inner ws_src) _
          _ = μ_src.toOuterMeasure {ws_src | ¬(L_anc a ws_src).slotSrc.GoodCovers} := by
              rw [PMF.toOuterMeasure_apply]
              refine tsum_congr fun ws_src => ?_
              by_cases hg : (L_anc a ws_src).slotSrc.GoodCovers <;> simp [hg]
          _ ≤ B_half := by
              refine uniform_seedWords_bad_le hUw hsrc_safe (evs_src a)
                (fun ws => (L_anc a ws).slotSrc)
                (fun ws => (hf a ha ws).2.2.1) (fun ws => (hf a ha ws).2.2.2.1)
                (fun hc ws => (hf a ha ws).2.2.2.2.1 hc) fun hc => ?_
              let ws₀ := zeroSeedWords c w capSrc
              obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _⟩ := hf a ha ws₀
              have hb₀ := (dualCoreInv_slot_evs_bounds ha_inv₀).1
                (by rw [(ha_sch₀.2 hdrPhase (by decide) (by decide)).symm]
                    change ph ≤ 8; omega)
                (ha_nc₀ ▸ hc)
              rwa [ha_nc₀, ha_ev₀] at hb₀
          _ ≤ stepFailureProbWhp c s_dict (.query u) := half_stepFailureProb_le c s_dict (.query u)
      · rw [ite_eq_right hp5] at hregimes
        by_cases hp67 : ph = 6 ∨ ph = 7
        · rw [ite_eq_left hp67] at hregimes
          obtain ⟨α, μ_idx, evs_src, L_anc, s_anc, f67, hν, hf⟩ := hregimes
          rw [hν, PMF.bind_bind]
          refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
          rw [PMF.bind_bind]
          let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
          have h_inner : ∀ ws_src : SeedWords c w capSrc,
              (((PMF.uniformOfFintype (SeedWords c w capDst)).map (f67 a ws_src)).bind μ_step
                ).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ≤
              if (L_anc a ws_src).slotSrc.GoodCovers then 0 else 1 := fun ws_src => by
            obtain ⟨_, ha_sch, _, _, _, hwd⟩ := hf a ha ws_src
            by_cases hgc : (L_anc a ws_src).slotSrc.GoodCovers
            · rw [ite_eq_left hgc]
              refine toOuterMeasure_bind_le_const _ _ _ 0 fun t ht => ?_
              rw [PMF.mem_support_map_iff] at ht; obtain ⟨wd, _, rfl⟩ := ht
              obtain ⟨hr, hc67, hsl, _⟩ := hwd wd
              have hsch_t := ha_sch.trans hc67.1
              have hph_t : (f67 a ws_src wd).data.mem (base + hdrPhase) = ph :=
                (hsch_t.2 hdrPhase (by decide) (by decide)).symm
              obtain ⟨_, _, _, _, _, hT⟩ := hq_spec hr
              have hag : (f67 a ws_src wd).latent.ActiveGood
                  ((f67 a ws_src wd).data.mem (base + hdrPhase)) := by
                unfold DualLatent.ActiveGood
                rw [hph_t, hsl]
                exact ⟨fun _ => hgc, fun h8 => by rcases hp67 with h | h <;> omega⟩
              have htimed : (q_of (f67 a ws_src wd)).timed = true := by
                dsimp only [q_of]; rw [dite_eq_left hr]
              rw [PMF.toOuterMeasure_apply]
              refine (tsum_eq_zero_iff.mpr fun q => ?_).le
              by_cases hq_eq : q = q_of (f67 a ws_src wd)
              · subst hq_eq
                have hnot : q_of (f67 a ws_src wd) ∉
                    {q | ¬q.WithinBudget (worstCaseTimeWhp c)} := fun hnb =>
                  hnb ⟨htimed, hT hag⟩
                simp [hnot]
              · simp [μ_step, PMF.pure_apply, hq_eq]
            · rw [ite_eq_right hgc]; exact PMF.toOuterMeasure_le_one _ _
          calc (μ_src.bind _).toOuterMeasure _
              = ∑' ws_src, μ_src ws_src * _ := PMF.toOuterMeasure_bind_apply _ _ _
            _ ≤ ∑' ws_src, μ_src ws_src *
                  (if (L_anc a ws_src).slotSrc.GoodCovers then 0 else 1) :=
                tsum_le_tsum fun ws_src => mul_le_mul_right (h_inner ws_src) _
            _ = μ_src.toOuterMeasure {ws_src | ¬(L_anc a ws_src).slotSrc.GoodCovers} := by
                rw [PMF.toOuterMeasure_apply]
                refine tsum_congr fun ws_src => ?_
                by_cases hg : (L_anc a ws_src).slotSrc.GoodCovers <;> simp [hg]
            _ ≤ stepFailureProbWhp c s_dict (.query u) := by
                refine (uniform_seedWords_bad_le hUw hsrc_safe (evs_src a)
                  (fun ws => (L_anc a ws).slotSrc)
                  (fun ws => (hf a ha ws).2.2.1) (fun ws => (hf a ha ws).2.2.2.1)
                  (fun hc ws => (hf a ha ws).2.2.2.2.1 hc) fun hc => ?_).trans
                  (half_stepFailureProb_le c s_dict (.query u))
                let ws₀ := zeroSeedWords c w capSrc
                obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _⟩ := hf a ha ws₀
                have hb₀ := (dualCoreInv_slot_evs_bounds ha_inv₀).1
                  (by rw [(ha_sch₀.2 hdrPhase (by decide) (by decide)).symm]
                      change ph ≤ 8; rcases hp67 with h | h <;> omega)
                  (ha_nc₀ ▸ hc)
                rwa [ha_nc₀, ha_ev₀] at hb₀
        · rw [ite_eq_right hp67] at hregimes
          by_cases hp8 : ph = 8
          · rw [ite_eq_left hp8] at hregimes
            obtain ⟨α, μ_idx, evs_src, evs_dst, L_anc, s_anc, f8, hν, hf⟩ := hregimes
            have hdst_safe := dualNDst_safe hinv_rep (by change ph ≠ 0; omega)
            rw [hν, PMF.bind_bind]
            refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
            let μ_src := PMF.uniformOfFintype (SeedWords c w capSrc)
            let μ_dst := PMF.uniformOfFintype (SeedWords c w capDst)
            let μ_prod : PMF (SeedWords c w capSrc × SeedWords c w capDst) :=
              μ_src.bind fun ws => μ_dst.map (ws, ·)
            have hbind_eq :
                ((μ_src.bind fun ws => μ_dst.map (f8 a ws)).bind μ_step) =
                  μ_prod.map (fun p => q_of (f8 a p.1 p.2)) := by
              dsimp only [μ_prod, μ_step]
              rw [PMF.bind_bind, PMF.map_bind]
              refine congrArg (μ_src.bind ·) (funext fun ws => ?_)
              rw [PMF.bind_map, PMF.map_comp]
              unfold PMF.map; rfl
            rw [hbind_eq, PMF.toOuterMeasure_map_apply]
            let BadS : Set (SeedWords c w capSrc × SeedWords c w capDst) :=
              {p | ¬(L_anc a p.1).slotSrc.GoodCovers}
            let BadD : Set (SeedWords c w capSrc × SeedWords c w capDst) :=
              {p | ¬(f8 a p.1 p.2).latent.slotDst.GoodCovers}
            have hsub : (fun p : SeedWords c w capSrc × SeedWords c w capDst =>
                q_of (f8 a p.1 p.2)) ⁻¹' {q | ¬q.WithinBudget (worstCaseTimeWhp c)} ⊆
                BadS ∪ BadD := by
              intro ⟨ws, wd⟩ hbad
              by_cases hgs : (L_anc a ws).slotSrc.GoodCovers
              · refine Or.inr fun hgd => hbad ?_
                obtain ⟨_, ha_sch, _, _, _, _, hwd⟩ := hf a ha ws
                obtain ⟨hr, hc8, hsl, _⟩ := hwd wd
                obtain ⟨_, _, _, _, _, hT⟩ := hq_spec hr
                have htimed : (q_of (f8 a ws wd)).timed = true := by
                  dsimp only [q_of]; rw [dite_eq_left hr]
                exact ⟨htimed, hT ⟨fun _ => hsl.symm ▸ hgs, fun _ => hgd⟩⟩
              · exact Or.inl hgs
            have hm_s : μ_prod.toOuterMeasure BadS ≤
                if U < whpThreshold c then 0
                else ((1 : ℝ≥0∞) / 2) *
                  (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
              have hfst : μ_prod.map Prod.fst = μ_src := by
                dsimp only [μ_prod]
                rw [PMF.map_bind]
                conv_rhs => rw [← PMF.bind_pure μ_src]
                refine congrArg (μ_src.bind ·) (funext fun ws => ?_)
                rw [PMF.map_comp]; exact PMF.map_const μ_dst ws
              have heq_s : μ_prod.toOuterMeasure BadS =
                  μ_src.toOuterMeasure {ws | ¬(L_anc a ws).slotSrc.GoodCovers} := by
                rw [← hfst, PMF.toOuterMeasure_map_apply]; rfl
              rw [heq_s]
              refine uniform_seedWords_bad_le hUw hsrc_safe (evs_src a)
                (fun ws => (L_anc a ws).slotSrc)
                (fun ws => (hf a ha ws).2.2.1) (fun ws => (hf a ha ws).2.2.2.1)
                (fun hc ws => (hf a ha ws).2.2.2.2.1 hc) fun hc => ?_
              let ws₀ := zeroSeedWords c w capSrc
              obtain ⟨ha_inv₀, ha_sch₀, ha_nc₀, ha_ev₀, _, _, _⟩ := hf a ha ws₀
              have hb₀ := (dualCoreInv_slot_evs_bounds ha_inv₀).1
                (by rw [(ha_sch₀.2 hdrPhase (by decide) (by decide)).symm]; change ph ≤ 8; omega)
                (ha_nc₀ ▸ hc)
              rwa [ha_nc₀, ha_ev₀] at hb₀
            have hm_d : μ_prod.toOuterMeasure BadD ≤
                if U < whpThreshold c then 0
                else ((1 : ℝ≥0∞) / 2) *
                  (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
              refine toOuterMeasure_bind_le_const μ_src _ BadD _ fun ws _ => ?_
              rw [PMF.toOuterMeasure_map_apply]
              refine uniform_seedWords_bad_le hUw hdst_safe (evs_dst a ws)
                (fun wd => (f8 a ws wd).latent.slotDst)
                (fun wd => (hf a ha ws).2.2.2.2.2.2 wd |>.2.2.2.1)
                (fun wd => (hf a ha ws).2.2.2.2.2.2 wd |>.2.2.2.2.2.1)
                (fun hc wd => (hf a ha ws).2.2.2.2.2.2 wd |>.2.2.2.2.2.2 hc) fun hc => ?_
              let wd₀ := zeroSeedWords c w capDst
              obtain ⟨hr₀, hc8₀, _, hdn₀, _, hde₀, _⟩ := (hf a ha ws).2.2.2.2.2.2 wd₀
              have hsch₀ := (hf a ha ws).2.1.trans hc8₀.1
              have hb₀ := (dualCoreInv_slot_evs_bounds hr₀.2.2.2).2
                (by rw [(hsch₀.2 hdrPhase (by decide) (by decide)).symm]; change 8 ≤ ph; omega)
                (hdn₀ ▸ hc)
              rwa [hdn₀, hde₀] at hb₀
            calc μ_prod.toOuterMeasure _
                ≤ μ_prod.toOuterMeasure (BadS ∪ BadD) := μ_prod.toOuterMeasure.mono hsub
              _ ≤ μ_prod.toOuterMeasure BadS + μ_prod.toOuterMeasure BadD :=
                  MeasureTheory.measure_union_le BadS BadD
              _ ≤ _ := add_le_add hm_s hm_d
              _ = stepFailureProbWhp c s_dict (.query u) :=
                  two_half_stepFailureProb_eq c s_dict (.query u)
          · rw [ite_eq_right hp8] at hregimes
            have hp9 : 9 ≤ ph := by omega
            have hdst_safe := dualNDst_safe hinv_rep (by change ph ≠ 0; omega)
            obtain ⟨α, μ_idx, evs_of, f_act, hν, hf⟩ := hregimes
            rw [hν, PMF.bind_bind]
            refine toOuterMeasure_bind_le_const μ_idx _ _ _ fun a ha => ?_
            rw [PMF.bind_map]
            refine (toOuterMeasure_map_pure_le _ _ _
              (fun wd => (f_act a wd).latent.slotDst.GoodCovers) fun wd hgc hbad => ?_).trans ?_
            · obtain ⟨hr, hsch, _, _, _⟩ := hf a ha wd
              obtain ⟨_, _, _, _, _, hT⟩ := hq_spec hr
              have hph_t : (f_act a wd).data.mem (base + hdrPhase) = ph :=
                (hsch.2 hdrPhase (by decide) (by decide)).symm
              have hag : (f_act a wd).latent.ActiveGood
                  ((f_act a wd).data.mem (base + hdrPhase)) := by
                unfold DualLatent.ActiveGood
                rw [hph_t]; exact ⟨fun h8 => absurd (hp9.trans h8) (by decide), fun _ => hgc⟩
              have htimed : (q_of (f_act a wd)).timed = true := by
                dsimp only [q_of]; rw [dite_eq_left hr]
              exact hbad ⟨htimed, hT hag⟩
            · refine (uniform_seedWords_bad_le hUw hdst_safe (evs_of a)
                (fun wd => (f_act a wd).latent.slotDst)
                (fun wd => (hf a ha wd).2.2.1) (fun wd => (hf a ha wd).2.2.2.1)
                (fun hc wd => (hf a ha wd).2.2.2.2 hc) fun hc => ?_).trans
                (half_stepFailureProb_le c s_dict (.query u))
              let wd₀ := zeroSeedWords c w capDst
              obtain ⟨hr₀, hsch₀, hnc₀, hev₀, _⟩ := hf a ha wd₀
              change (f_act a wd₀).latent.slotDst.nCap = _ at hnc₀
              change (f_act a wd₀).latent.slotDst.evs = _ at hev₀
              have hb₀ := (dualCoreInv_slot_evs_bounds hr₀.2.2.2).2
                (by rw [(hsch₀.2 hdrPhase (by decide) (by decide)).symm]; change 8 ≤ ph; omega)
                (hnc₀ ▸ hc)
              rwa [hnc₀, hev₀] at hb₀

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
