/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian
public import CslibFrontier.Algorithms.WordRAM.Hungarian.Regs
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Algorithms.WordRAM.Hungarian.Argmin
import CslibFrontier.Algorithms.WordRAM.Hungarian.Augment
import CslibFrontier.Algorithms.WordRAM.Hungarian.Dual
import CslibFrontier.Algorithms.WordRAM.Hungarian.Extend
import CslibFrontier.Algorithms.WordRAM.Hungarian.Init
import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith

/-!
# In-memory `O(n³)` Hungarian solver (`coreCode` and `core_exec`)

Assembles alternating-tree phases into `coreCode` and proves its `O(n³)` Word-RAM execution bound
`core_exec` on an unsigned/shifted row-major cost matrix.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- One tree-growing or augmenting round of phase `rr`. -/
private def roundBody : Code .standard 28 :=
  .seq argminCode
    (.seq dualCode
      (.seq (ram[ addr ← baseColMate + rj1; ri0 ← *addr ])
        (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])))

/-- Complete alternating-tree phase rooted at free row `rr`. -/
private def phaseCode : Code .standard 28 :=
  .seq initPhaseCode (.loop (.eq augmented zero) roundBody)

private theorem exec_phaseCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (hr_free : r ∉ matchedLeft (mateMatching mate₀))
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w phaseCode x y (99 * n * n + 60 * n + 17) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      HgOuterBound (fun p => (C p : ℤ)) W
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).y
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).z
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate ∧
      matchedLeft (mateMatching (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate) =
        insert r (matchedLeft (mateMatching mate₀)) ∧
      OuterMem bC
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).y
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).z
        (hgPhase (fun p => (C p : ℤ)) y₀ z₀ mate₀ r).mate y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  have hc_bounds : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W :=
    fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩
  let s_end := hgPhase c y₀ z₀ mate₀ r
  obtain ⟨y_init, he_init, hr_init, haug_init, hSM_init, hf_init⟩ :=
    exec_initPhaseCode hCW hOB r x hb hC hOM hr_reg hfit
  let I (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) ∧
      ((y.regs augmented = 1 ∧
          HgOuterBound c W s_end.y s_end.z s_end.mate ∧
          matchedLeft (mateMatching s_end.mate) = insert r (matchedLeft (mateMatching mate₀)) ∧
          OuterMem bC s_end.y s_end.z s_end.mate y.mem) ∨
       (y.regs augmented = 0 ∧
          ∃ (s : HgState n) (bestRow : Fin n → Fin n) (fuel : ℕ),
            s.mate = mate₀ ∧
            fuel + usedCount s.used = n ∧
            0 < fuel ∧
            HgStepInv c W r s bestRow ∧
            StepMem bC s bestRow y.mem ∧
            hgLoop c fuel s = s_end))
  let rank (y : Data 28) : ℕ :=
    if y.regs augmented = 0 then
      n - (Finset.univ.filter fun j : Fin n => y.mem (bC + n * n + 3 * n + j.val) = 1).card
    else 0
  have hused_card_eq : ∀ {s : HgState n} {bestRow : Fin n → Fin n} {m : ℕ → ℕ},
      StepMem bC s bestRow m →
      (Finset.univ.filter fun j : Fin n => m (bC + n * n + 3 * n + j.val) = 1).card =
        usedCount s.used := by
    intro s bestRow m hSM
    unfold usedCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hSM.hused j]
    cases vget s.used j <;> simp
  have hstepRound (y : Data 28) (hy : I y) (hc : (Cond.eq augmented zero).Holds y) :
      ∃ z, ExecWithin w roundBody y z (94 * n + 28) ∧ I z ∧ rank z < rank y := by
    obtain ⟨hr, hf, hstate⟩ := hy
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have haug0 : y.regs augmented = 0 := by simpa only [Cond.holds_eq, hby.hzero] using hc
    rcases hstate with ⟨h1, _⟩ |
        ⟨_, s, bestRow, fuel, hs_mate, hfuel_eq, hfuel_pos, hSI, hSM, hloop_eq⟩
    · omega
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfuel_pos)
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf a (by omega)
    obtain ⟨y₁, j₁, he₁, hr₁, hmem₁, harg, hrj1₁, hrdel₁⟩ := exec_argminCode hSI y hby hSM hfit
    obtain ⟨hj₁_unused, hmin⟩ := hgArgmin_some harg
    have hb₁ : BaseRegs n bC M y₁ := hby.of_eq fun i hi => hr₁ i (by omega)
    have hSM₁ : StepMem bC s bestRow y₁.mem := hmem₁ ▸ hSM
    obtain ⟨y₂, he₂, hr₂, hSM₂, hf₂⟩ :=
      exec_dualCode hCW hSI hj₁_unused hmin y₁ hb₁ hSM₁ hrdel₁ hfit
    have hSD := hgStepInv_dual hc_bounds hSI hj₁_unused hmin
    have hz_j₁ : vget (hgDual s (vget s.minv j₁)).minv j₁ = 0 := by
      rw [hgDual_minv, hj₁_unused, ite_eq_right Bool.false_ne_true, sub_self]
    have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
    have hrj1₂ : y₂.regs rj1 = j₁.val := (hr₂ rj1 (by decide)).trans hrj1₁
    have hcm_j₁ : y₂.mem (bC + n * n + 2 * n + j₁.val) = encodeOptFin (vget s.mate j₁) := by
      simpa only [hgDual_mate] using hSM₂.hcol j₁
    have hstep₃ : ∃ y₃, ExecWithin w (ram[ addr ← baseColMate + rj1; ri0 ← *addr ]) y₂ y₃ 2 ∧
        (∀ i : Fin 28, i.val < 20 → y₃.regs i = y₂.regs i) ∧
        y₃.mem = y₂.mem ∧
        y₃.regs ri0 = encodeOptFin (vget s.mate j₁) := by
      refine WP.exists_execWithin ?_
      have := j₁.isLt
      wram_exec [hb₂.hbaseColMate, hrj1₂, hcm_j₁]
      exact ⟨fun i hi => by wram_simp, rfl, by wram_simp⟩
    obtain ⟨y₃, he₃, hr₃, hmem₃, hri0₃⟩ := hstep₃
    have hb₃ : BaseRegs n bC M y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
    have hrj1₃ : y₃.regs rj1 = j₁.val := (hr₃ rj1 (by decide)).trans hrj1₂
    have hSM₃ : StepMem bC (hgDual s (vget s.minv j₁)) bestRow y₃.mem := hmem₃ ▸ hSM₂
    have hout₃ : ∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y₃.mem a = x.mem a := fun a ha =>
      (congrFun hmem₃ a).trans ((hf₂ a (by omega)).trans ((congrFun hmem₁ a).trans (hf a ha)))
    cases hm : vget s.mate j₁ with
    | none =>
      have hri0_n : y₃.regs ri0 = n := by simpa [hm, encodeOptFin] using hri0₃
      have hmate_d : vget (hgDual s (vget s.minv j₁)).mate j₁ = none := by
        simpa only [hgDual_mate] using hm
      obtain ⟨hOB', hL'⟩ := hgOuterBound_augment hSD hj₁_unused hz_j₁ hmate_d
      obtain ⟨y₄, he₄, hr₄, haug₄, hOM₄, hf₄⟩ :=
        exec_augmentCode hSD hj₁_unused hz_j₁ hmate_d y₃ hb₃ hSM₃ hrj1₃ hfit
      have hbr : ExecWithin w (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])
          y₃ y₄ (22 * n + 11) := by
        obtain ⟨t, ht, hex⟩ := he₄
        exact ⟨t + 1, by omega, .branch_pos (by simp [Cond.holds_eq, hri0_n, hb₃.hrn]) hex⟩
      have hsend : { (hgDual s (vget s.minv j₁)) with
          mate := hgApplyEdges (hgDual s (vget s.minv j₁)).mate
            (vget (hgDual s (vget s.minv j₁)).path j₁) } = s_end := by
        simp [← hloop_eq, hgLoop, harg, hm]
      refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq hbr))).mono (by omega),
        ⟨fun i hi => ?_, fun a ha => (hf₄ a (by omega)).trans (hout₃ a ha),
          .inl ⟨haug₄, ?_, ?_, ?_⟩⟩, ?_⟩
      · rw [hr₄ i hi, hr₃ i (by omega), hr₂ i (by omega), hr₁ i (by omega), hr i hi]
      · simpa only [← hsend] using hOB'
      · simpa only [← hsend, hgDual_mate, hs_mate] using hL'
      · simpa only [← hsend] using hOM₄
      · simp only [rank, haug0, haug₄, one_ne_zero, ↓reduceIte, hused_card_eq hSM]
        omega
    | some i₀ =>
      have hri0_i : y₃.regs ri0 = i₀.val := by simpa [hm, encodeOptFin] using hri0₃
      have hri0_ne : y₃.regs ri0 ≠ n := by rw [hri0_i]; exact ne_of_lt i₀.isLt
      have hmate_d : vget (hgDual s (vget s.minv j₁)).mate j₁ = some i₀ := by
        simpa only [hgDual_mate] using hm
      have hSE := hgStepInv_extend hc_bounds hSD hj₁_unused hz_j₁ hmate_d
      have hC₃ : CostMem bC C y₃.mem := hC.of_outside fun a ha => hout₃ a (by omega)
      obtain ⟨y₄, he₄, hr₄, hSM₄, hf₄⟩ :=
        exec_extendCode hCW hSD y₃ hb₃ hC₃ hSM₃ hrj1₃ hri0_i hfit
      have hbr : ExecWithin w (ram[ if ri0 = rn then [ ⟪augmentCode⟫ ] else [ ⟪extendCode⟫ ] ])
          y₃ y₄ (48 * n + 12) := by
        obtain ⟨t, ht, hex⟩ := he₄
        exact ⟨t + 2, by omega, .branch_neg (by simp [Cond.holds_eq, hri0_ne, hb₃.hrn]) hex⟩
      have haug₄ : y₄.regs augmented = 0 :=
        ((((hr₄ augmented (by decide)).trans (hr₃ augmented (by decide))).trans
          (hr₂ augmented (by decide))).trans (hr₁ augmented (by decide))).trans haug0
      have hcnt' : usedCount (hgExtend c (hgDual s (vget s.minv j₁)) j₁ i₀).used =
          usedCount s.used + 1 := by
        rw [hgExtend_used, hgDual_used]
        exact usedCount_vset hj₁_unused
      have hfuel'_pos : 0 < fuel' := by
        have h1 := usedCount_le hSE.matching hSE.used_mate
        have h2 := card_lt_of_root_free hSE.matching hSE.root_free
        omega
      refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq hbr))).mono (by omega),
        ⟨fun i hi => ?_, fun a ha => (hf₄ a (by omega)).trans (hout₃ a ha),
          .inr ⟨haug₄, _, _, fuel', by rw [hgExtend_mate, hgDual_mate, hs_mate],
            by omega, hfuel'_pos, hSE, hSM₄, by simp [← hloop_eq, hgLoop, harg, hm]⟩⟩, ?_⟩
      · rw [hr₄ i (by omega), hr₃ i (by omega), hr₂ i (by omega), hr₁ i (by omega), hr i hi]
      · simp only [rank, haug0, haug₄, ↓reduceIte, hused_card_eq hSM, hused_card_eq hSM₄]
        rw [hcnt']; omega
  have hI_init : I y_init := by
    have hcnt0 : usedCount (hgInit c y₀ z₀ mate₀ r).used = 0 := by simp [usedCount, hgInit_used]
    refine ⟨hr_init, fun a ha => hf_init a (by omega),
      .inr ⟨haug_init, hgInit c y₀ z₀ mate₀ r, fun _ => r, n, rfl, by omega, r.pos,
        hgStepInv_init hc_bounds hOB hr_free, hSM_init, rfl⟩⟩
  have hrank_init : rank y_init ≤ n := by
    dsimp only [rank]
    split_ifs
    omega
  obtain ⟨y, hl, hIy, hcy⟩ := ExecWithin.loop_invariant
    (cond := .eq augmented zero) (body := roundBody) I rank (T := 94 * n + 28) hstepRound hI_init
  obtain ⟨hr, hf, hstate⟩ := hIy
  have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
  rcases hstate with ⟨_, hOB_end, hL_end, hOM_end⟩ | ⟨haug0, _⟩
  · refine ⟨y, (he_init.seq hl).mono ?_, hr, hOB_end, hL_end, hOM_end, hf⟩
    have := Nat.mul_le_mul_right (94 * n + 28 + 2) hrank_init
    nlinarith
  · exact absurd (Cond.holds_eq.mpr (haug0.trans hby.hzero.symm)) hcy

/-- Run `phaseCode` and increment `rr`. -/
private def phasesBody : Code .standard 28 :=
  .seq phaseCode (ram[ rr ← rr + one ])

/-- Run all `n` alternating-tree phases (`rr = 0 .. n - 1`). -/
private def phasesCode : Code .standard 28 :=
  .seq (ram[ rr ← #0 ]) (.loop (.lt rr rn) phasesBody)

private theorem hgRows_append_singleton {n : ℕ} (c : Fin n × Fin n → ℤ)
    (rs : List (Fin n)) (r : Fin n) (s : HgState n) :
    hgRows c (rs ++ [r]) s =
      hgPhase c (hgRows c rs s).y (hgRows c rs s).z (hgRows c rs s).mate r := by
  induction rs generalizing s with
  | nil => rfl
  | cons a rs ih => exact ih (hgPhase c s.y s.z s.mate a)

/-- Instruction bound for `coreCode` (`O(n³)`). -/
@[expose] def coreTime (n : ℕ) : ℕ :=
  99 * n ^ 3 + 70 * n ^ 2 + 48 * n + 16

/-- Core `O(n³)` Hungarian solver on an in-memory `n × n` unsigned cost matrix `C` at `baseC`:
initializes row potentials `y`, column potentials `nz`, and mates, runs `n` augmenting phases, and
writes length `n` at `outBase`. -/
def coreCode : Code .standard 28 :=
  .seq initOuterCode (.seq phasesCode (ram[ *outBase ← rn ]))

/-- **`O(n³)` Word-RAM execution on an in-memory unsigned/shifted cost matrix.** Given `BaseRegs`
and `CostMem` for an `n × n` matrix `C : Fin n × Fin n → ℕ` bounded by `W` at `bC`, `coreCode`
halts within `coreTime n = O(n³)` instructions at every word width satisfying
`Fits w (bC + n * n + 8 * n + 2 * W + 2)`, leaving `(hungarian fun p => (C p : ℤ))`'s potentials
and perfect matching in memory. -/
theorem core_exec {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
    let out := hungarian c
    ∃ y, ExecWithin w coreCode x y (coreTime n) ∧
      (∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) ∧
      (∀ u : Fin n, (y.mem (bC + n * n + u.val) : ℤ) = out.y u) ∧
      (∀ v : Fin n, -(y.mem (bC + n * n + n + v.val) : ℤ) = out.z v) ∧
      y.mem (bC + n * n + 7 * n) = n ∧
      (∀ u : Fin n, ∃ v : Fin n, y.mem (bC + n * n + 7 * n + 1 + u.val) = v.val ∧
        (u, v) ∈ out.matching) ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 8 * n + 1 ≤ a → y.mem a = x.mem a) := by
  intro c out
  have hc_bounds : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W :=
    fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩
  obtain ⟨y₁, he₁, hr₁, hOM₁, hf₁⟩ := exec_initOuterCode hCW x hb hC hfit
  let s₀ := hgStartState (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0) (Vector.replicate n none)
  let sAt (k : ℕ) : HgState n := hgRows c ((List.finRange n).take k) s₀
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 16 → y.regs i = x.regs i) ∧
      HgOuterBound c W (sAt k).y (sAt k).z (sAt k).mate ∧
      matchedLeft (mateMatching (sAt k).mate) = ((List.finRange n).take k).toFinset ∧
      OuterMem bC (sAt k).y (sAt k).z (sAt k).mate y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs rr) y) (hlt : y.regs rr < n) :
      ∃ z, ExecWithin w phasesBody y z (99 * n * n + 60 * n + 18) ∧
        P (y.regs rr + 1) z ∧ z.regs rr = y.regs rr + 1 := by
    obtain ⟨hr, hOB_k, hL_k, hOM_k, hf_k⟩ := hy
    let r : Fin n := ⟨y.regs rr, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq hr
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf_k a (by omega)
    have hr_free : r ∉ matchedLeft (mateMatching (sAt (y.regs rr)).mate) := by
      rw [hL_k, List.mem_toFinset, List.mem_take_iff_getElem]
      rintro ⟨m, hm, heq⟩
      have : m = y.regs rr := by simpa [r] using congrArg Fin.val heq
      omega
    obtain ⟨y_p, he_p, hr_p, hOB_p, hL_p, hOM_p, hf_p⟩ :=
      exec_phaseCode hCW hOB_k r hr_free y hby hCy hOM_k rfl hfit
    have hrr_p : y_p.regs rr = y.regs rr := hr_p rr (by decide)
    have hone_p : y_p.regs one = 1 := (hr_p one (by decide)).trans hby.hone
    obtain ⟨z, he_inc, rfl⟩ : ∃ z,
        ExecWithin w (ram[ rr ← rr + one ] : Code .standard 28) y_p z 1 ∧
        z = y_p.set rr (y.regs rr + 1) := by
      refine WP.exists_execWithin ?_
      wram_exec [hrr_p, hone_p]
      rfl
    have hs_succ : sAt (y.regs rr + 1) =
        hgPhase c (sAt (y.regs rr)).y (sAt (y.regs rr)).z (sAt (y.regs rr)).mate r := by
      simp only [sAt, List.take_succ_finRange hlt, hgRows_append_singleton, r]
    refine ⟨_, (he_p.seq he_inc).mono (by omega), ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, by wram_simp⟩
    · wram_simp [hr_p i (by omega), hr i hi]
    · rwa [hs_succ]
    · rw [hs_succ, hL_p, hL_k, List.take_succ_finRange hlt]
      exact Finset.ext fun u => by simp [r]
    · change OuterMem bC _ _ _ y_p.mem
      rwa [hs_succ]
    · exact fun a ha => (hf_p a ha).trans (hf_k a ha)
  have hL0 : matchedLeft (mateMatching (Vector.replicate n (none : Option (Fin n)))) = ∅ :=
    Finset.ext fun u => by simp [mem_matchedLeft, mem_mateMatching, vget_replicate]
  obtain ⟨y₃, hl₃, hr₃, hOB_n, hL_n, hOM_n, hf₃⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := y₁)
    ⟨fun i hi => by wram_simp [hr₁ i (by omega)],
      hgOuterBound_start hc_bounds, hL0, hOM₁, hf₁⟩
  have hb₃ : BaseRegs n bC M y₃ := hb.of_eq hr₃
  obtain ⟨y₄, he₄, rfl⟩ : ∃ y₄,
      ExecWithin w (ram[ *outBase ← rn ] : Code .standard 28) y₃ y₄ 1 ∧
      y₄ = y₃.write (bC + n * n + 7 * n) n := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₃.houtBase, hb₃.hrn]
    rfl
  have hs_n : sAt n = hgRows c (List.finRange n) s₀ := by
    simp [sAt, List.take_of_length_le List.length_finRange.le]
  have hL_univ : matchedLeft (mateMatching (hgRows c (List.finRange n) s₀).mate) = Finset.univ :=
    Finset.ext fun u => by simp [← hs_n, hL_n, List.take_of_length_le List.length_finRange.le]
  have hm_eq : out.matching = mateMatching (hgRows c (List.finRange n) s₀).mate := by
    ext ⟨u, v⟩
    simp [out, hungarian, s₀, mem_foldl_hkMatchingStep, mem_mateMatching]
  refine ⟨_, (he₁.seq (hl₃.seq he₄)).mono ?_, hr₃,
    fun u => ?_, fun v => ?_, by simp, fun u => ?_, fun a ha => ?_⟩
  · unfold coreTime
    nlinarith
  · change (Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + u.val) : ℤ) = _
    rw [Function.update_of_ne (by have := u.isLt; omega), hOM_n.hy u, hs_n]
    exact Int.toNat_of_nonneg ((hs_n ▸ hOB_n).y_bounds u).1
  · change -(Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + n + v.val) : ℤ) = _
    rw [Function.update_of_ne (by have := v.isLt; omega), hOM_n.hnz v, hs_n,
      Int.toNat_of_nonneg (neg_nonneg.mpr ((hs_n ▸ hOB_n).z_bounds v).2), neg_neg]
    rfl
  · obtain ⟨v, hv⟩ := mem_matchedLeft.mp
      (hs_n.symm ▸ hL_univ.symm ▸ Finset.mem_univ u : u ∈ matchedLeft (mateMatching (sAt n).mate))
    refine ⟨v, ?_, hm_eq.symm ▸ hs_n ▸ hv⟩
    change Function.update y₃.mem (bC + n * n + 7 * n) n (bC + n * n + 7 * n + 1 + u.val) = v.val
    rw [Function.update_of_ne (by omega)]
    exact hOM_n.hrow_some v u (mem_mateMatching.mp hv)
  · change Function.update y₃.mem (bC + n * n + 7 * n) n a = x.mem a
    rw [Function.update_of_ne (by omega)]
    exact hf₃ a (by omega)

end Cslib.Algorithms.WordRAM.Hungarian
