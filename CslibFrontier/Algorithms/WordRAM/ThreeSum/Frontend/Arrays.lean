/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Program
import CslibFrontier.Computability.WordRAM.MemoryView
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc

/-!
# Native frontend array and descriptor execution

## Main results

The compact scan contract is composed with every array setup and descriptor store.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays

open Cslib.WordRAM Select Scan

/-- Local arithmetic budget covers array addresses, native labels and loop setup. -/
def budget (l : Layout) (U : ℕ) : ℕ := l.endpoint + 8 * U + 8 * l.digits + 64

/-- The hypotheses of a concrete compact scan, before choosing its bit coordinates and mode. -/
structure ScanReady (w : ℕ) (rs : List (ℕ × ℕ)) (x : Data 48) : Prop where
  /-- The source length is the distinct-key count. -/
  length : x.regs len = rs.length
  /-- Native small constants. -/
  constants : x.regs zero = 0 ∧ x.regs one = 1 ∧ x.regs two = 2 ∧
    x.regs three = 3 ∧ x.regs four = 4 ∧ x.regs five = 5
  /-- Both radix arrays have exact contents. -/
  keys : Block.HoldsList (x.regs Scan.keys) (rs.map Prod.fst) x.mem
  counts : Block.HoldsList (x.regs Scan.counts) (rs.map Prod.snd) x.mem
  /-- Every key and the native label arithmetic fit. -/
  words : ∀ p ∈ rs, Fits w p.1
  absolute : ∀ p ∈ rs, p.1 / 2 ≤ 2 * x.regs magnitude
  double : ∀ p ∈ rs, Fits w (2 * p.1)
  labels : Fits w (4 * x.regs magnitude + 2)
  small : Fits w 5
  /-- Source and output endpoints fit. -/
  keyAddress : Fits w (x.regs Scan.keys + rs.length)
  countAddress : Fits w (x.regs Scan.counts + rs.length)
  outputAddress : Fits w (x.regs dst + rs.length + 1)
  /-- Both source blocks precede the output. -/
  keysBefore : x.regs Scan.keys + rs.length ≤ x.regs dst
  countsBefore : x.regs Scan.counts + rs.length ≤ x.regs dst

/-- Parameters changed by split/mode setup. -/
def ScanParametersPreserved (x y : Data 48) : Prop :=
  y.mem = x.mem ∧ ∀ j, j.val < 27 → j ≠ beta → j ≠ beta' → j ≠ digit → j ≠ mode →
    y.regs j = x.regs j

/-- A mode/bit setup preserves every actual scan precondition. -/
theorem ScanReady.transfer {w : ℕ} {rs : List (ℕ × ℕ)} {x y : Data 48}
    (h : ScanReady w rs x) (he : ScanParametersPreserved x y) : ScanReady w rs y := by
  obtain ⟨hm, hr⟩ := he
  have eq (j : Fin 48) (hlt : j.val < 27 := by decide)
      (hj : j ≠ beta ∧ j ≠ beta' ∧ j ≠ digit ∧ j ≠ mode := by decide) :
      y.regs j = x.regs j := hr j hlt hj.1 hj.2.1 hj.2.2.1 hj.2.2.2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  simp only [← eq len, ← eq zero, ← eq one, ← eq two, ← eq three, ← eq four, ← eq five,
    ← eq Scan.keys, ← eq Scan.counts, ← eq magnitude, ← eq dst, ← hm]
    at h1 h2 h3 h4 h6 h8 h10 h11 h12 h13 h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Invoke the proved native scan from its actual arithmetic/layout context. -/
theorem ScanReady.exec {w : ℕ} {rs : List (ℕ × ℕ)} {x : Data 48}
    (h : ScanReady w rs x) :
    ∃ y, ExecWithin w Scan.program x y (43 * rs.length + 4) ∧
      Block.HoldsList (x.regs dst) (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) (x.regs mode) rs) y.mem ∧
      y.regs out = (Math.select (x.regs magnitude) (x.regs beta)
        (x.regs beta') (x.regs digit) (x.regs mode) rs).length ∧
      Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem y.mem ∧
      (∀ j, Scan.body.Preserves j → y.regs j = x.regs j) :=
  Scan.exec rs x h.length h.constants.1 h.constants.2.1 h.constants.2.2.1
    h.constants.2.2.2.1 h.constants.2.2.2.2.1 h.constants.2.2.2.2.2
    h.keys h.counts h.words h.absolute h.double h.labels h.small h.keyAddress
    h.countAddress h.outputAddress h.keysBefore h.countsBefore

private theorem exec_singleton {w : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (h : ScanReady w rs x) :
    ∃ y, ExecWithin w singleton x y 2 ∧
      Block.HoldsList (x.regs dst) [0] y.mem ∧ y.regs out = 1 ∧
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem y.mem := by
  unfold singleton
  wram_exec [h.constants.1, h.constants.2.1]
  wram_simp
  refine ⟨fun i => by simp [Block.read], fun a ha => ?_⟩
  apply Function.update_of_ne (fun he => ha ?_)
  simp only [Block.mem_footprint, Block.Owns]; omega

/-- Select exactly the array named by one physical slot. Every split/multiplicity setup is
executed; the width and label budget are scalar runtime values, independent of code size. -/
theorem pick_exec {w U Λ j : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (h : ScanReady w rs x) (hU : x.regs magnitude = U)
    (hΛ : x.regs digits = Λ) (hs : x.regs splits = 2 * Λ ^ 2)
    (ht : x.regs triple = j / 3) (hslot : x.regs slot = j % 3)
    (hjfit : Fits w j) :
    ∃ y, ExecWithin w pick x y (43 * rs.length + 20) ∧
      Block.HoldsList (x.regs dst) (Math.array U Λ rs j) y.mem ∧
      y.regs out = (Math.array U Λ rs j).length ∧
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem y.mem := by
  obtain ⟨hz, h1, h2, h3, h4, h5⟩ := h.constants
  have frame {mem : ℕ → ℕ}
      (hf : Modifies (Block.mk (x.regs dst) rs.length).footprint x.mem mem) :
      Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem mem :=
    fun a ha => hf a fun hmem => ha (by
      simp only [Block.mem_footprint, Block.Owns] at hmem ⊢; omega)
  have hsmall := h.small
  refine WP.exists_execWithin ?_
  unfold pick split splitSetup extra
  by_cases hsplit : j / 3 < 2 * Λ ^ 2
  · have hΛpos : 0 < Λ := by nlinarith
    have hmod_le : j / 3 / 2 % Λ ≤ j := (Nat.mod_le _ _).trans (by omega)
    have hdiv_le : j / 3 / 2 / Λ ≤ j := (Nat.div_le_self _ _).trans (by omega)
    wram_exec [h2, ht, hslot, hΛ, hs, hsplit]
    wram_call (ScanReady.exec (h.transfer (y := _)
      ⟨rfl, fun i _ hb hb' hv hm => by wram_simp [hb, hb', hv, hm]⟩))
      with y ⟨hm, ho, hf, _⟩
    have he : Math.array U Λ rs j = Math.select U (j / 3 / 2 / Λ)
        (j / 3 / 2 % Λ) (j / 3 % 2) (j % 3) rs := by
      simp [Math.array, Math.mode, Math.beta, Math.beta', Math.digit, hsplit,
        show j % 3 ≠ 6 by omega]
    wram_simp [hU, ← he] at hm ho
    exact ⟨by omega, hm, ho, frame hf⟩
  · let post (p : ℕ → Prop) (y : Data 48) (t : ℕ) : Prop :=
      p t ∧
        Block.HoldsList (x.regs dst) (Math.array U Λ rs j) y.mem ∧
        y.regs out = (Math.array U Λ rs j).length ∧
        Modifies (Block.mk (x.regs dst) (rs.length + 1)).footprint x.mem y.mem
    have runExtra (m : ℕ) {p : ℕ → Prop}
        (hp : ∀ t ≤ 43 * rs.length + 4, p t)
        (he : Math.array U Λ rs j =
          Math.select U (x.regs beta) (x.regs beta') (x.regs digit) m rs) :
        WP w Scan.program (x.set mode m) (post p) := by
      wram_call (ScanReady.exec (h.transfer ⟨rfl, fun _ _ _ _ _ hm => by wram_simp [hm]⟩))
        with y ⟨hm, ho, hf, _⟩
      wram_simp [hU, ← he] at hm ho hf
      exact ⟨hp _ (by omega), hm, ho, frame hf⟩
    have runSingle {p : ℕ → Prop} (hp : ∀ t ≤ 2, p t)
        (he : Math.array U Λ rs j = [0]) :
        WP w singleton x (post p) := by
      wram_call (exec_singleton x rs h) with y ⟨hm, ho, hf⟩
      exact ⟨hp _ (by omega), he ▸ hm, by simpa only [he, List.length_singleton] using ho, hf⟩
    wram_exec [hz, h1, h3, h4, h5, ht, hslot, hs, hsplit]
    · apply runExtra 3 <;> [omega; simp [Math.array, Math.mode, Math.select_extra, *]]
    · apply runSingle <;> [omega; simp [Math.array, Math.mode, *]]
    · apply runExtra 5 <;> [omega; simp [Math.array, Math.mode, Math.select_extra, *]]
    · apply runExtra 4 <;> [omega; simp [Math.array, Math.mode, Math.select_extra, *]]
    · apply runSingle <;> [omega; simp [Math.array, Math.mode, *]]

/-- One complete array, its exact descriptor words, allocation advance and local frame. -/
theorem body_exec {w U Λ j : ℕ} (x : Data 48) (rs : List (ℕ × ℕ))
    (hready : ScanReady w rs (x.set dst (x.regs heap)))
    (hU : x.regs magnitude = U) (hΛ : x.regs digits = Λ)
    (hs : x.regs splits = 2 * Λ ^ 2) (hj : x.regs current = j)
    (hcap : rs.length + 1 ≤ x.regs capacity)
    (hbefore : x.regs descriptors + 2 * j + 2 ≤ x.regs heap)
    (ha : Fits w (x.regs descriptors + 2 * j + 2))
    (hh : Fits w (x.regs heap + x.regs capacity)) (hi : Fits w (j + 1)) :
    ∃ y, ExecWithin w body x y (43 * rs.length + 30) ∧
      y.regs current = j + 1 ∧ y.regs heap = x.regs heap + x.regs capacity ∧
      y.mem (x.regs descriptors + 2 * j) = (Math.array U Λ rs j).length ∧
      y.mem (x.regs descriptors + 2 * j + 1) = x.regs heap ∧
      Block.HoldsList (x.regs heap) (Math.array U Λ rs j) y.mem ∧
      (∀ a, (a < x.regs heap ∨ x.regs heap + x.regs capacity ≤ a) →
        a ≠ x.regs descriptors + 2 * j → a ≠ x.regs descriptors + 2 * j + 1 →
        y.mem a = x.mem a) := by
  have h1 : x.regs one = 1 := by simpa +decide using hready.constants.2.1
  have h3 : x.regs three = 3 := by simpa +decide using hready.constants.2.2.2.1
  have hj3_le : j % 3 ≤ j + 1 := (Nat.mod_le _ _).trans (by omega)
  refine WP.exists_execWithin ?_
  unfold body writeDescriptor
  wram_exec [h3, hj]
  have hr : ScanReady w rs (((x.set triple (j / 3)).set slot (j % 3)).set dst (x.regs heap)) := by
    refine hready.transfer ⟨rfl, fun i hil _ _ _ _ => ?_⟩
    have hit : i ≠ triple := fun h => by subst i; norm_num [triple] at hil
    have his : i ≠ slot := fun h => by subst i; norm_num [slot] at hil
    by_cases hid : i = dst
    · subst i; wram_simp
    · wram_simp [hid, hit, his]
  wram_call (pick_exec (U := U) (Λ := Λ) (j := j) _ rs hr ..) framed [hU, hΛ, hs]
    with v m ⟨hmem, hout, hf⟩
  wram_exec [h1, hj, hout]
  have haddr : j + j + x.regs descriptors = x.regs descriptors + 2 * j := by omega
  wram_simp [haddr]
  refine ⟨by ram_keep hmem, fun b hb hb0 hb1 => ?_⟩
  wram_simp [hb0, hb1]
  exact hf b fun hfp => by simp only [Block.mem_footprint, Block.Owns] at hfp; omega

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays
