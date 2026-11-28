/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# One charged native tile-count update

## Main results

* `Wanted.exec_countStep`: load the actual pair, compute its tile and increment exactly
  that bucket while preserving original query memory and all other counts.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A row-major tile key, computed from the two original coordinate words. -/
def tileKey (L m N : ℕ) (q : ℕ × ℕ) : ℕ :=
  bandOf L m q.1 * numBands L m N + bandOf L m q.2

/-- Admitted original positions always name one of the actual tiles. -/
theorem tileKey_lt {L m N : ℕ} (hm : m ≤ L) (q : ℕ × ℕ)
    (hr : q.1 < N) (hc : q.2 < N) : tileKey L m N q < numBands L m N ^ 2 := by
  have hβ := bandOf_lt_numBands hm N q.1 hr
  have hγ := bandOf_lt_numBands hm N q.2 hc
  unfold tileKey
  nlinarith only [Nat.mul_le_mul_right (numBands L m N) (Nat.succ_le_of_lt hβ), hγ]

/-- The full native count update, including loading both original coordinates. Its count
bound comes from the original prefix length, rather than a supplied intermediate-state fit. -/
theorem exec_countStep {w L m N Q n : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hn : n < Q) (hpair : (pairs n).1 < N ∧ (pairs n).2 < N) (x : Data 96)
    (hx : Parameters L m N Q x) (hi : x.regs index = n)
    (hinput : x.mem (5 + 2 * n) = (pairs n).1 ∧
      x.mem (5 + 2 * n + 1) = (pairs n).2)
    (hcounts : ∀ t < numBands L m N ^ 2,
      x.mem (countAddress L Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) n)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w countStep x y 14 ∧ Parameters L m N Q y ∧ y.regs index = n + 1 ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (countAddress L Q + t) =
          Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) (n + 1)) ∧
      (∀ a, a < countAddress L Q ∨ countAddress L Q + numBands L m N ^ 2 ≤ a →
        y.mem a = x.mem a) := by
  let I := (pairs n).1
  let J := (pairs n).2
  let B := numBands L m N
  let β := bandOf L m I
  let γ := bandOf L m J
  let key := tileKey L m N ∘ pairs
  let c := Nat.count (fun k => key k = key n) n
  have ht : key n < B ^ 2 := tileKey_lt hm _ hpair.1 hpair.2
  have hβ : β < B := bandOf_lt_numBands hm N I hpair.1
  have hγ : γ < B := bandOf_lt_numBands hm N J hpair.2
  have hB : B ≤ B ^ 2 := Nat.le_self_pow (by decide) B
  have hBeq : B ^ 2 = numBands L m N ^ 2 := rfl
  have h10 := Nat.zero_le (10 ^ L)
  have hprod : β * B ≤ key n := Nat.le_add_right _ _
  have hcle : c ≤ n := Nat.count_le _
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q) : Fits w v := hl.of_le (by omega)
  have hcn : Fits w (c + 1) := hf _ (by omega)
  have hn1 : Fits w (n + 1) := hf _ (by omega)
  have hn2 : Fits w (n * 2) := hf _ (by omega)
  have ha : Fits w (n * 2 + 5) := hf _ (by omega)
  have ha1 : Fits w (n * 2 + 5 + 1) := hf _ (by omega)
  have hβf : Fits w β := hf _ (by omega)
  have hγf : Fits w γ := hf _ (by omega)
  have hpf : Fits w (β * B) := hf _ (by omega)
  have hkf : Fits w (key n) := hf _ (by omega)
  have hcf : Fits w (countAddress L Q + key n) :=
    hf _ (by unfold countAddress tableAddress inputLimit; omega)
  have hload : x.mem (countAddress L Q + key n) = c := hcounts _ ht
  obtain ⟨hI, hJ⟩ : x.mem (n * 2 + 5) = I ∧ x.mem (n * 2 + 5 + 1) = J := by
    simpa only [Nat.mul_comm n 2, Nat.add_comm (2 * n) 5] using hinput
  dsimp only [β, γ, B, I, J, bandOf] at hβf hγf hpf
  dsimp only [I, J] at hI hJ
  dsimp only [key, Function.comp_def, tileKey, bandOf] at hkf hcf hload
  refine WP.exists_execWithin ?_
  wram_exec * [countStep, loadQuery, tileCode,
    hI, hJ, hload, hn2, ha, ha1, hβf, hγf, hpf, hkf, hcf, hcn, hn1]
  refine ⟨by regs_frame, by wram_simp, fun t ht' => ?_, fun a ha' => ?_⟩
  · rw [Nat.count_succ]
    by_cases h : key n = t
    · subst h
      dsimp only [key, Function.comp_def, tileKey, bandOf]; wram_simp; rfl
    · have hne : countAddress L Q + t ≠
          countAddress L Q + ((pairs n).1 / bandSize L m * numBands L m N +
            (pairs n).2 / bandSize L m) := by
        dsimp only [key, Function.comp_def, tileKey, bandOf] at h
        omega
      wram_simp [hne, hcounts t ht']
      dsimp only [key] at h
      rw [ite_eq_right h, Nat.add_zero]
  · have hne : a ≠ countAddress L Q + ((pairs n).1 / bandSize L m * numBands L m N +
        (pairs n).2 / bandSize L m) := by
      change a ≠ countAddress L Q + key n; omega
    wram_simp [hne]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
