/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Hungarian.Instance
public import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Input decoding, cost shifting, and output cost encoding subroutines

Internal `O(n²)` / `O(n)` pre- and post-processing steps (`setupCode`, `scanMaxCode`,
`fillCCode`, `sumCostCode`) around `coreCode` for `Data.init inst.encode`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Read `n = mem[1]` and set up all constants and array bases starting at `baseC = 2 + n * n`. -/
def setupCode : Code .standard 28 := ram[
  zero ← #0; one ← #1; two ← #2;
  rn ← *one; rnn ← rn * rn; rM ← #0;
  baseC ← two + rnn;
  baseY ← baseC + rnn;
  baseNZ ← baseY + rn;
  baseColMate ← baseNZ + rn;
  baseUsed ← baseColMate + rn;
  baseTree ← baseUsed + rn;
  baseMinv ← baseTree + rn;
  baseBestRow ← baseMinv + rn;
  outBase ← baseBestRow + rn;
  baseRowMate ← outBase + one ]

/-- Scan input words `2 .. 2 + n² - 1` for `rM = max |cost|`. -/
private def scanMaxBody : Code .standard 28 := ram[
  addr ← two + idx; val ← *addr; val ← val / two;
  if rM < val then [ rM ← val ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Compute `rM` across all `n²` encoded entries. -/
def scanMaxCode : Code .standard 28 :=
  .seq (ram[ rM ← #0; idx ← #0 ]) (.loop (.lt idx rnn) scanMaxBody)

/-- Decode `Signed.encode` word `2 + idx` and store shifted cost `(cost + rM).toNat` at
`baseC + idx`. -/
private def fillCBody : Code .standard 28 := ram[
  addr ← two + idx; val ← *addr;
  val2 ← val / two; tmp ← val % two;
  if tmp = zero then [ val ← rM + val2 ] else [ val ← rM - val2 ];
  addr ← baseC + idx; *addr ← val; idx ← idx + one ]

/-- Populate `[baseC, baseC + n²)` with nonnegative shifted costs. -/
def fillCCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rnn) fillCBody)

/-- Accumulate `C[idx, rowMate[idx]]` into `acc`. -/
private def sumCostBody : Code .standard 28 := ram[
  addr ← baseRowMate + idx; val ← *addr;
  addr ← idx * rn; addr ← addr + val; addr ← baseC + addr; val ← *addr;
  acc ← acc + val; idx ← idx + one ]

/-- Compute `Signed.encode` of the optimal unshifted matching cost into `acc`. -/
def sumCostCode : Code .standard 28 :=
  .seq (ram[ acc ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rn) sumCostBody)
      (ram[ val ← rn * rM;
            if acc < val then [
              val2 ← val - acc; acc ← two * val2; acc ← acc + one
            ] else [
              val2 ← acc - val; acc ← two * val2 ] ]))


theorem exec_setupCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound) :
    ∃ y₁, ExecWithin w setupCode (Data.init inst.encode) y₁ 16 ∧
      BaseRegs inst.n (2 + inst.n * inst.n) 0 y₁ ∧
      y₁.mem = (Data.init inst.encode : Data 28).mem := by
  have hmem1 : (Data.init inst.encode : Data 28).mem 1 = inst.n := inst.init_mem_n
  -- Every base address is at most `2 + 2 n² + 8 n + 1`, a linear bound in the atoms `n²` and `n`.
  have hfit : Fits w (2 + inst.n * inst.n + inst.n * inst.n + 8 * inst.n + 1) :=
    hw.of_le (by unfold Instance.wordBound; nlinarith)
  refine WP.exists_execWithin ?_
  unfold setupCode
  wram_exec [hmem1]
  refine ⟨?_, rfl⟩
  constructor <;> wram_simp <;> omega

theorem exec_scanMaxCode {w : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (y₁ : Data 28) (hb₁ : BaseRegs inst.n (2 + inst.n * inst.n) 0 y₁)
    (hmem₁ : y₁.mem = (Data.init inst.encode : Data 28).mem) :
    ∃ y₂, ExecWithin w scanMaxCode y₁ y₂ (9 * inst.n * inst.n + 4) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) (y₂.regs rM) y₂ ∧
      y₂.mem = (Data.init inst.encode : Data 28).mem ∧
      y₂.regs rM ≤ inst.maxMag ∧
      (∀ u v : Fin inst.n, (inst.cost (u, v)).natAbs ≤ y₂.regs rM) := by
  let n := inst.n
  let bC := 2 + n * n
  let x₀ : Data 28 := Data.init inst.encode
  let PM (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 16 → i ≠ rM → y.regs i = y₁.regs i) ∧
      y.mem = x₀.mem ∧
      y.regs rM ≤ inst.maxMag ∧
      (∀ q : ℕ, (hq : q < k) → (hq' : q < n * n) →
        (inst.cost (finProdFinEquiv.symm ⟨q, hq'⟩)).natAbs ≤ y.regs rM)
  have hbodyM (y : Data 28) (hy : PM (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w scanMaxBody y z 7 ∧ PM (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hM_le, hM_ge⟩ := hy
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    let u := p.1
    let v := p.2
    have hp_mul : u.val * n + v.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have htwo_y : y.regs two = 2 := (hr two (by decide) (by decide)).trans hb₁.htwo
    have hzero_y : y.regs zero = 0 := (hr zero (by decide) (by decide)).trans hb₁.hzero
    have hone_y : y.regs one = 1 := (hr one (by decide) (by decide)).trans hb₁.hone
    have hload : y.mem (2 + y.regs idx) = Signed.encode (inst.cost (u, v)) := by
      rw [hmem, ← hp_mul]
      exact inst.init_mem_cost u v
    have hdiv : Signed.encode (inst.cost (u, v)) / 2 = (inst.cost (u, v)).natAbs :=
      Signed.encode_div_two _
    have hmag_le : (inst.cost (u, v)).natAbs ≤ inst.maxMag := inst.natAbs_cost_le_maxMag u v
    have hfit : Fits w (2 + n * n + inst.maxMag) :=
      hw.of_le (by unfold Instance.wordBound; simp only [n]; nlinarith)
    refine WP.exists_execWithin ?_
    unfold scanMaxBody
    wram_exec [htwo_y, hzero_y, hone_y, hload, hdiv]
    all_goals
      refine ⟨⟨fun i hi hne => by wram_simp [hr i hi hne], hmem, ?_, fun q hq hq' => ?_⟩,
        by wram_simp⟩ <;> wram_simp
    · exact hmag_le
    · rcases eq_or_ne q (y.regs idx) with rfl | hne
      exacts [le_rfl, (hM_ge q (by omega) hq').trans (le_of_lt hc)]
    · exact hM_le
    · rcases eq_or_ne q (y.regs idx) with rfl | hne
      exacts [le_of_not_gt hc, hM_ge q (by omega) hq']
  have hs₀ : ∃ s₀,
      ExecWithin w (ram[ rM ← #0; idx ← #0 ] : Code .standard 28) y₁ s₀ 2 ∧
      PM 0 s₀ ∧ s₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨⟨fun i hi hne => by wram_simp, hmem₁, by wram_simp; exact Nat.zero_le _,
      fun _ hq _ => by omega⟩, by wram_simp⟩
  obtain ⟨s₀, hes₀, hPs₀, hidxs₀⟩ := hs₀
  obtain ⟨y₂, hl₂, hPn₂, _⟩ := ExecWithin.loop_count PM
    (fun y hy => (hy.1 rnn (by decide) (by decide)).trans hb₁.hrnn) hbodyM
    (by omega) (hidxs₀ ▸ hPs₀)
  obtain ⟨hr₂, hm₂, hM_le₂, hM_ge₂⟩ := hPn₂
  have hb₂ : BaseRegs n bC (y₂.regs rM) y₂ := by struct_frame hb₁
  refine ⟨y₂, (hes₀.seq hl₂).mono (by rw [hidxs₀, Nat.sub_zero]; nlinarith),
    hb₂, hm₂, hM_le₂, fun u v => ?_⟩
  have hq : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  have h := hM_ge₂ (u.val * n + v.val) hq hq
  have hp_eq : (⟨u.val * n + v.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (u, v) :=
    Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (u, v))
  rwa [hp_eq, finProdFinEquiv.symm_apply_apply] at h

theorem exec_fillCCode {w M : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (hM_le : M ≤ inst.maxMag) (hM_ge : ∀ u v : Fin inst.n, (inst.cost (u, v)).natAbs ≤ M)
    (y₂ : Data 28) (hb₂ : BaseRegs inst.n (2 + inst.n * inst.n) M y₂)
    (hmem₂ : y₂.mem = (Data.init inst.encode : Data 28).mem) :
    ∃ y₃, ExecWithin w fillCCode y₂ y₃ (12 * inst.n * inst.n + 3) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) M y₃ ∧
      CostMem (2 + inst.n * inst.n) (fun p => (inst.cost p + (M : ℤ)).toNat) y₃.mem := by
  let n := inst.n
  let bC := 2 + n * n
  let x₀ : Data 28 := Data.init inst.encode
  let C : Fin n × Fin n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  let eC : ℕ → ℕ := fun q => if hq : q < n * n then C (finProdFinEquiv.symm ⟨q, hq⟩) else 0
  let PC (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = y₂.regs i) ∧
      (∀ j < k, y.mem (bC + j) = eC j) ∧
      (∀ a, ¬(bC ≤ a ∧ a < bC + k) → y.mem a = x₀.mem a)
  have hbodyC (y : Data 28) (hy : PC (y.regs idx) y) (hlt : y.regs idx < n * n) :
      ∃ z, ExecWithin w fillCBody y z 10 ∧ PC (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    have hby : BaseRegs n bC M y := hb₂.of_eq fun i hi => hr i (by omega)
    let p := finProdFinEquiv.symm ⟨y.regs idx, hlt⟩
    let u := p.1
    let v := p.2
    have hp_mul : u.val * n + v.val = y.regs idx :=
      (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv p).trans
        (congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨y.regs idx, hlt⟩))
    have hload : y.mem (2 + y.regs idx) = Signed.encode (inst.cost (u, v)) := by
      rw [hf _ (by simp only [bC]; omega), ← hp_mul]
      exact inst.init_mem_cost u v
    have hdiv : Signed.encode (inst.cost (u, v)) / 2 = (inst.cost (u, v)).natAbs :=
      Signed.encode_div_two _
    have hmod : Signed.encode (inst.cost (u, v)) % 2 = if inst.cost (u, v) < 0 then 1 else 0 :=
      Signed.encode_mod_two _
    have hmag_M : (inst.cost (u, v)).natAbs ≤ M := hM_ge u v
    have hmag := inst.natAbs_cost_le_maxMag u v
    have hCuv : eC (y.regs idx) = (inst.cost (u, v) + (M : ℤ)).toNat := by
      simp only [eC, hlt, dite_true]; rfl
    have hfitB : Fits w (bC + n * n) :=
      hw.of_le (by unfold Instance.wordBound; simp only [bC, n]; nlinarith)
    have hfitM : Fits w (2 * inst.maxMag) := hw.of_le (by unfold Instance.wordBound; nlinarith)
    have hstep : ∃ z, ExecWithin w fillCBody y z 10 ∧
        z.mem = Function.update y.mem (bC + y.regs idx) (eC (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = y₂.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold fillCBody
      by_cases hneg : inst.cost (u, v) < 0 <;> simp only [hneg, ↓reduceIte] at hmod
      all_goals
        wram_exec [hby.htwo, hby.hzero, hby.hone, hby.hrM, hby.hbaseC, hload, hdiv, hmod]
        exact ⟨by wram_simp [hCuv]; congr 1; omega, fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y₃, he₃, hr₃, hm₃, _⟩ := exec_forLoop PC
    (fun y hy => (hy.1 rnn (by decide)).trans hb₂.hrnn) hbodyC (x := y₂)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun a _ => congrFun hmem₂ a⟩
  refine ⟨y₃, he₃.mono (by nlinarith),
    hb₂.of_eq (fun i hi => hr₃ i (by omega)), fun u v => ?_⟩
  have hq : u.val * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
  have h := hm₃ (u.val * n + v.val) hq
  have hp_eq : (⟨u.val * n + v.val, hq⟩ : Fin (n * n)) = finProdFinEquiv (u, v) :=
    Fin.ext (Cslib.Matrix.pairIndex_eq_val_finProdFinEquiv (u, v))
  dsimp only [eC, n, bC, C] at h
  rw [dite_eq_left hq, hp_eq, finProdFinEquiv.symm_apply_apply] at h
  exact h

theorem exec_sumCostCode {w M : ℕ} (inst : Instance) (hw : Fits w inst.wordBound)
    (hM_le : M ≤ inst.maxMag)
    (hC_cast : ∀ p : Fin inst.n × Fin inst.n,
      (((inst.cost p + (M : ℤ)).toNat : ℕ) : ℤ) = inst.cost p + (M : ℤ))
    (hC_le : ∀ u v : Fin inst.n, (inst.cost (u, v) + (M : ℤ)).toNat ≤ 2 * M)
    (y₄ : Data 28) (hb₄ : BaseRegs inst.n (2 + inst.n * inst.n) M y₄)
    (hC₄ : CostMem (2 + inst.n * inst.n) (fun p => (inst.cost p + (M : ℤ)).toNat) y₄.mem)
    (hrm_eq : ∀ u : Fin inst.n,
      y₄.mem ((2 + inst.n * inst.n) + inst.n * inst.n + 7 * inst.n + 1 + u.val) =
        (inst.assignedCol u).val) :
    ∃ y₆, ExecWithin w sumCostCode y₄ y₆ (10 * inst.n + 10) ∧
      BaseRegs inst.n (2 + inst.n * inst.n) M y₆ ∧
      y₆.mem = y₄.mem ∧
      y₆.regs acc = inst.encodedMinCost := by
  let n := inst.n
  let bC := 2 + n * n
  let C : Fin n × Fin n → ℕ := fun p => (inst.cost p + (M : ℤ)).toNat
  have hfit_core : Fits w (bC + n * n + 8 * n + 2 * (2 * M) + 2) :=
    hw.of_le (by unfold Instance.wordBound; simp only [bC, n]; nlinarith)
  let PS (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = y₄.regs i) ∧
      y.mem = y₄.mem ∧
      y.regs acc = (((List.finRange n).take k).map fun u => C (u, inst.assignedCol u)).sum ∧
      y.regs acc ≤ k * (2 * M)
  have hbodyS (y : Data 28) (hy : PS (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w sumCostBody y z 8 ∧ PS (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hacc_eq, hacc_le⟩ := hy
    let u : Fin n := ⟨y.regs idx, hlt⟩
    let v := inst.assignedCol u
    have hby : BaseRegs n bC M y := hb₄.of_eq fun i hi => hr i (by omega)
    have hrm_u : y.mem (bC + n * n + 7 * n + 1 + y.regs idx) = v.val := by
      rw [hmem]
      exact hrm_eq u
    have hmul : y.regs idx * n + v.val < n * n := Cslib.Matrix.pairIndex_lt (u, v)
    have hC_uv : y.mem (bC + (y.regs idx * n + v.val)) = C (u, v) := by
      rw [hmem]
      exact hC₄ u v
    have hC_uv_le : C (u, v) ≤ 2 * M := hC_le u v
    have hf5 : Fits w (y.regs acc + C (u, v)) :=
      hw.of_le (by
        have h1 : y.regs acc + C (u, v) ≤ (y.regs idx + 1) * (2 * M) := by nlinarith
        have h2 : (y.regs idx + 1) * (2 * M) ≤ n * (2 * inst.maxMag) :=
          Nat.mul_le_mul (by omega) (by omega)
        unfold Instance.wordBound
        simp only [n] at h2
        nlinarith)
    refine WP.exists_execWithin ?_
    unfold sumCostBody
    wram_exec [hby.hbaseRowMate, hby.hrn, hby.hbaseC, hby.hone, hrm_u, hC_uv]
    refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
    · wram_simp
      rw [List.take_succ_finRange hlt, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton, ← hacc_eq]
    · wram_simp
      nlinarith
  have hs_init : ∃ s₀,
      ExecWithin w (ram[ acc ← #0; idx ← #0 ] : Code .standard 28) y₄ s₀ 2 ∧
      PS 0 s₀ ∧ s₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    exact ⟨⟨fun i hi => by wram_simp, rfl, by wram_simp; simp,
      by wram_simp; exact Nat.zero_le _⟩, by wram_simp⟩
  obtain ⟨s₀_sum, hes_sum, hPS₀, hidx_sum⟩ := hs_init
  obtain ⟨y₅, hl_sum, hPSn, _⟩ := ExecWithin.loop_count PS
    (fun y hy => (hy.1 rn (by decide)).trans hb₄.hrn) hbodyS (by omega) (hidx_sum ▸ hPS₀)
  obtain ⟨hr₅, hmem₅, hacc₅, hacc₅_le⟩ := hPSn
  have hb₅ : BaseRegs n bC M y₅ := hb₄.of_eq fun i hi => hr₅ i (by omega)
  have hsum_z : (y₅.regs acc : ℤ) =
      matchingCost inst.cost (hungarian inst.cost).matching + (n * M : ℕ) := by
    have htake : (List.finRange n).take n = List.finRange n :=
      List.take_of_length_le (by simp)
    have hfin_sum : ((List.finRange n).map fun u => C (u, inst.assignedCol u)).sum =
        ∑ u : Fin n, C (u, inst.assignedCol u) := by
      rw [← Fin.sum_univ_def]
    rw [htake, hfin_sum] at hacc₅
    rw [hacc₅, Nat.cast_sum]
    simp only [C, hC_cast]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      inst.sum_cost_assignedCol]
    push_cast
    ring
  set opt := matchingCost inst.cost (hungarian inst.cost).matching
  have hnM : n * M ≤ n * inst.maxMag := Nat.mul_le_mul_left n hM_le
  have hacc_le : y₅.regs acc ≤ 2 * (n * M) := hacc₅_le.trans_eq (by ring)
  have hfit_enc : Fits w (2 * (2 * (n * inst.maxMag)) + 1) :=
    hw.of_le (by unfold Instance.wordBound; simp only [n]; nlinarith)
  have hstep_enc : ∃ y₆,
      ExecWithin w
        (ram[ val ← rn * rM;
              if acc < val then [
                val2 ← val - acc; acc ← two * val2; acc ← acc + one
              ] else [
                val2 ← acc - val; acc ← two * val2 ] ] : Code .standard 28) y₅ y₆ 6 ∧
      (∀ i : Fin 28, i.val < 16 → y₆.regs i = y₅.regs i) ∧
      y₆.mem = y₄.mem ∧
      y₆.regs acc = Signed.encode opt := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₅.hrn, hb₅.hrM, hb₅.htwo, hb₅.hone]
    all_goals
      refine ⟨fun i hi => by wram_simp, hmem₅, ?_⟩
      wram_simp
      unfold Signed.encode
      split_ifs <;> omega
  obtain ⟨y₆, he_enc, hr₆, hmem₆, hacc₆⟩ := hstep_enc
  exact ⟨y₆, (hes_sum.seq (hl_sum.seq he_enc)).mono (by rw [hidx_sum]; omega),
    hb₅.of_eq hr₆, hmem₆, hacc₆⟩


end Cslib.Algorithms.WordRAM.Hungarian
