/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Input
public import CslibFrontier.Computability.WordRAM.FlatEndpoint

/-!
# Initialized halting caller-safe box fixed-prime computation

The same final state witnesses the actual initialized prefix, halt, verdict, original
coordinates and global failed-scan accounting. Fourteen real header/pointer instructions
precede the complete caller program, and the final halt is charged. This remains a fixed-prime
component with explicit thin geometry, not parameter/prime selection or the 3SUM endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Numerical envelope for initialized prefix words and newly written addresses. -/
@[expose] def prefixBound (n d g p : ℕ) (values : List ℤ) : ℕ :=
  wordBound n d g p (rawTotal n values) (workspaceBase n) (inputWordBound n d g p values)

/-- Minimum-width `FlatEndpoint` certificate for the initialized callable fixed-prime solver. -/
theorem entry_endpoint {m n g p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u v : Fin n => V (n * n + pairIndex (u, v))
    let wAC := fun u v : Fin n => V (2 * (n * n) + pairIndex (u, v))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64,
      Instances.Output n (D m) g p V
        (.init (PreparationInput.input n (D m) g p values)) a ∧
      FlatEndpoint entryProgram Reg.found
        (fun _ : Unit => inputWidth n (D m) g p values)
        (fun _ => prefixBound n (D m) g p values)
        (fun _ => PreparationInput.input n (D m) g p values)
        (fun _ => 14 + timeBound (m := m) hn g p values a.mem)
        (fun _ y =>
          (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
          y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
          (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
          (y.regs Reg.found = 1 → ∃ u v c : Fin n,
            y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
            y.regs Reg.witnessC = c.val ∧ weightSum wAB wBC wAC u v c = 0) ∧
          (∀ q, q < workspaceBase n ∨
            workspaceBase n + windowSize n (D m) g p (rawTotal n values) ≤ q →
            y.mem q = (Data.init (PreparationInput.input n (D m) g p values) : Data 640).mem q) ∧
          ∀ j : Fin 640, j.val < 160 → y.regs j = 0) := by
  let T := rawTotal n values
  let M := windowSize n (D m) g p T
  let b := workspaceBase n
  let wMin := inputWidth n (D m) g p values
  have fit : Fits wMin (b + 4 * M + 4 * M + 1024) := admission_fits le_rfl
  have fit_win : Fits wMin (b + 4 * M + 1024) := fit.of_le (by omega)
  obtain ⟨-, hw_src, -, hS, -, hc⟩ :=
    MemoryWindow.dynamicWidth_fits (b := b) (widthCoeff := 6166) (S := n + D m + g + p + T + 4)
      (by decide) (by omega) (fit_win.of_le (Nat.le_add_right _ 1024))
  have hiMin : InputFits wMin (PreparationInput.input n (D m) g p values) :=
    (input_fits_source (m := m) (g := g) (p := p) values hlen
      (natAbs_le_rawTotal values hlen)).mono hw_src
  have hS_M : n + D m + g + p + T + 4 ≤ M := hS
  have hinitfit : Fits wMin (n + D m + g + p + 5 + 3 * (n * n) + 1024) :=
    fit.of_le (by dsimp only [b, workspaceBase] at *; omega)
  obtain ⟨x, hinit, xmem, xn, xD, xg, xp, xab, xbc, xac, xb⟩ := exec_entryHeader values hinitfit
  have hx : x.Bounded wMin := hinit.bounded (Data.Bounded.init hiMin)
  have word (q : ℕ) : x.mem (5 + q) = Signed.encode (values.getD q 0) :=
    (congrFun xmem _).trans (PreparationInput.input_word n (D m) g p values q)
  obtain ⟨a, hout, y, hy, -, yf, ys, yiff, yw, yframe, -⟩ := exec values hlen hD hg hp hN
    x xn xD xg xp xb (by rw [xab]; dsimp only [workspaceBase]; omega)
    (by rw [xbc]; dsimp only [workspaceBase]; omega)
    (by rw [xac]; dsimp only [workspaceBase]; omega)
    (fun q _ => by rw [xab]; exact word q)
    (fun q _ => by rw [xbc]; simpa only [Nat.add_assoc] using word (n * n + q))
    (fun q _ => by rw [xac]; simpa only [two_mul, Nat.add_assoc] using word (2 * (n * n) + q))
    hx (fit.of_le (by dsimp only [b, M, T] at *; omega))
  have he := hinit.seq hy
  refine ⟨a, hout,
    { not_readsWidth := not_or.mpr ⟨entryHeader_fixed.2, program_not_readsWidth⟩
      inputFits_min := fun _ => hiMin
      two_pow_wMin_le := fun _ =>
        pow_admissionWidth_le n (D m) g p T b (inputWordBound n (D m) g p values)
      exec_min := fun _ => ⟨y, he, yf, ys, yiff, fun hf => ?_,
        fun q hq => (yframe q hq).trans (congrFun xmem q),
        fun j hj => he.regs_eq (entryProgram_preserves_selector j hj)⟩ }⟩
  obtain ⟨ha, hb, hc, hz⟩ := yw hf
  exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl, rfl, rfl, hz⟩

/-- Fully initialized same-state prefix and halt. The width guarantee also establishes original
input fit; no producer state, prepared catalogue, layout, solver or run law is an input. -/
theorem runs_input {W m n g p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hW : inputWidth n (D m) g p values ≤ W) :
    let V := fun q => values.getD q 0
    let wAB := fun u v : Fin n => V (pairIndex (u, v))
    let wBC := fun u v : Fin n => V (n * n + pairIndex (u, v))
    let wAC := fun u v : Fin n => V (2 * (n * n) + pairIndex (u, v))
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    InputFits W (PreparationInput.input n (D m) g p values) ∧
      ∃ a : Data 64,
        Instances.Output n (D m) g p V
          (.init (PreparationInput.input n (D m) g p values)) a ∧
        ∃ y t, t + 1 ≤ timeBound (m := m) hn g p values a.mem + 15 ∧
          Runs W (entryProgram.program Reg.found)
            (State.init (PreparationInput.input n (D m) g p values)) ⟨entryProgram.size, y⟩ t ∧
          Executes W (entryProgram.program Reg.found)
            (State.init (PreparationInput.input n (D m) g p values)) (y.regs Reg.found) (t + 1) ∧
          y.Bounded W ∧ (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
          y.regs Reg.scans ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
          (y.regs Reg.found = 1 ↔ HasZeroTriangle wAB wBC wAC) ∧
          (y.regs Reg.found = 1 → ∃ u v c : Fin n,
            y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
            y.regs Reg.witnessC = c.val ∧ weightSum wAB wBC wAC u v c = 0) ∧
          (∀ q, q < workspaceBase n ∨
            workspaceBase n + windowSize n (D m) g p (rawTotal n values) ≤ q →
            y.mem q = (Data.init (PreparationInput.input n (D m) g p values) : Data 640).mem q) ∧
          ∀ j : Fin 640, j.val < 160 → y.regs j = 0 := by
  obtain ⟨a, hout, E⟩ := entry_endpoint values hlen hD hg hp hN
  obtain ⟨y, t, ht, hruns, hexec, ybound, yf, ys, yiff, yw, yframe, ysel⟩ := E.runs () hW
  exact ⟨E.inputFits () hW, a, hout, y, t, by omega, hruns, hexec, ybound,
    yf, ys, yiff, yw, yframe, ysel⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
