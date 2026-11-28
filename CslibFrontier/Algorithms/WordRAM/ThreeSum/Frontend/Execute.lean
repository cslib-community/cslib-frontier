/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Frontend.Arrays
import CslibFrontier.Computability.WordRAM.MemoryView

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Complete descriptor-table execution

The invariant retains every completed descriptor and compact payload, both full radix arrays,
and all memory outside the allocated frontend region.

## Main results

The enumeration loop charges each native array scan, descriptor store and allocation advance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays

open Cslib.WordRAM Select Scan

/-- Immutable registers of the complete enumeration loop. -/
structure Registers (l : Layout) (U k : ℕ) (x : Data 48) : Prop where
  /-- Original magnitude promise. -/
  magnitude : x.regs Select.magnitude = U
  /-- Original input length and explicit bit budget. -/
  inputLen : x.regs Arrays.inputLen = l.n
  digits : x.regs Arrays.digits = l.digits
  /-- Exact radix key/count pointers and distinct-key length. -/
  keys : x.regs Scan.keys = 1 + 2 * l.n
  counts : x.regs Scan.counts = 1 + 3 * l.n
  len : x.regs Scan.len = k
  /-- Computed layout values. -/
  splits : x.regs Arrays.splits = l.splits
  triples : x.regs Arrays.triples = l.count
  arrays : x.regs Arrays.arrays = l.arrays
  capacity : x.regs Arrays.capacity = l.capacity
  descriptors : x.regs Arrays.descriptors = l.descriptors
  heapEnd : x.regs Arrays.heapEnd = l.endpoint
  /-- All small constants are real native registers. -/
  constants : x.regs zero = 0 ∧ x.regs one = 1 ∧ x.regs two = 2 ∧
    x.regs three = 3 ∧ x.regs four = 4 ∧ x.regs five = 5

/-- The body preserves every immutable layout and source register. -/
theorem Registers.transfer {l : Layout} {U k : ℕ} {x y : Data 48}
    (h : Registers l U k x) (hr : ∀ i, body.Preserves i → y.regs i = x.regs i) :
    Registers l U k y := by
  regs_frame

/-- Every layout scalar and partial allocation is below the explicit arithmetic budget. -/
theorem layout_bounds (l : Layout) (U : ℕ) :
    l.n + 1 ≤ budget l U ∧ l.digits * l.digits ≤ budget l U ∧
    l.splits ≤ budget l U ∧ l.count ≤ budget l U ∧ l.arrays ≤ budget l U ∧
    2 * l.arrays ≤ budget l U ∧ l.payloads ≤ budget l U ∧
    l.arrays * l.capacity ≤ budget l U ∧ l.endpoint ≤ budget l U ∧
    4 * U + 2 ≤ budget l U ∧ 5 ≤ budget l U := by
  have hmul : l.arrays * l.capacity = l.capacity * l.arrays := Nat.mul_comm _ _
  have hsq : l.digits * l.digits = l.digits ^ 2 := (pow_two _).symm
  dsimp only [budget, Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors,
    Layout.splits, Layout.count, Layout.arrays] at hmul ⊢
  omega

/-- Setup computes all constants and addresses with actual instructions, preserving all memory. -/
theorem setup_exec {w U : ℕ} (l : Layout) (k : ℕ) (x : Data 48)
    (hU : x.regs Select.magnitude = U) (hn : x.regs inputLen = l.n)
    (hΛ : x.regs digits = l.digits) (hk : x.regs Scan.keys = 1 + 2 * l.n)
    (hc : x.regs Scan.counts = 1 + 3 * l.n) (hlen : x.regs len = k)
    (hd : x.regs descriptors = l.descriptors) (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w setup x y 19 ∧ Registers l U k y ∧
      y.regs current = 0 ∧ y.regs heap = l.pointer 0 ∧ y.mem = x.mem := by
  have hf (v : ℕ) (hv : v ≤ budget l U) : Fits w v := hfit.of_le hv
  refine WP.exists_execWithin ?_
  wram_exec (disch := (
    try dsimp only [budget, Layout.endpoint, Layout.pointer, Layout.payloads,
      Layout.descriptors, Layout.capacity, Layout.arrays, Layout.count, Layout.splits]
    try ring_nf
    omega)) [setup, hn, hΛ, hd, hf]
  wram_simp
  refine ⟨?_, ?_⟩
  · constructor
    all_goals wram_simp
    all_goals
      first
      | assumption
      | trivial
      | (dsimp only [Layout.splits, Layout.count, Layout.arrays,
          Layout.capacity, Layout.endpoint, Layout.pointer, Layout.payloads]; ring)
  · dsimp only [Layout.pointer, Layout.payloads, Layout.arrays, Layout.count, Layout.splits]
    ring

/-- All compact arrays and six-word descriptors are produced by the complete native loop. -/
theorem loop_exec {w U : ℕ} (l : Layout) (rs : List (ℕ × ℕ)) (x : Data 48)
    (hr : Registers l U rs.length x) (hidx : x.regs current = 0)
    (hheap : x.regs heap = l.pointer 0) (hlen : rs.length ≤ l.n)
    (hk : Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) x.mem)
    (hc : Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) x.mem)
    (hkeys : ∀ p ∈ rs, p.1 ≤ 2 * U + 1 ∧ p.1 / 2 ≤ U)
    (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w (.loop (.lt current arrays) body) x y
        (l.arrays * (43 * rs.length + 32) + 2) ∧
      Output l U rs y.mem ∧ y.regs current = l.arrays ∧ y.regs heap = l.endpoint ∧
      Registers l U rs.length y ∧
      Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
      Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem := by
  obtain ⟨-, -, -, -, ha_bd, -, -, -, he, hlabel, hsmall⟩ := layout_bounds l U
  have hbase : l.descriptors ≤ l.pointer 0 := by dsimp [Layout.pointer, Layout.payloads]; omega
  have hN : 1 + 4 * l.n ≤ l.endpoint := by
    dsimp only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors]
    omega
  let P (j : ℕ) (y : Data 48) : Prop :=
    Registers l U rs.length y ∧
    y.regs heap = l.pointer j ∧
    (∀ i < j,
      y.mem (l.descriptors + 2 * i) = (Math.array U l.digits rs i).length ∧
      y.mem (l.descriptors + 2 * i + 1) = l.pointer i ∧
      Block.HoldsList (l.pointer i) (Math.array U l.digits rs i) y.mem) ∧
    Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
    Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
    Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem
  have hbody (y : Data 48) (hy : P (y.regs current) y) (hj : y.regs current < l.arrays) :
      ∃ z, ExecWithin w body y z (43 * rs.length + 30) ∧ P (y.regs current + 1) z ∧
        z.regs current = y.regs current + 1 := by
    obtain ⟨hyr, hyheap, hyout, hykeys, hycounts, hyframe⟩ := hy
    have hnext : l.pointer (y.regs current + 1) ≤ l.endpoint :=
      l.pointer_mono (by omega)
    have hcur : l.pointer (y.regs current) ≤ l.endpoint := l.pointer_mono (by omega)
    have hcappos : 0 < l.capacity := by dsimp [Layout.capacity]; omega
    have hsource : 1 + 4 * l.n ≤ l.pointer (y.regs current) := by
      have := l.pointer_mono (i := 0) (j := y.regs current) (by omega)
      change l.descriptors ≤ _
      omega
    have hnext_cap : l.pointer (y.regs current) + (l.n + 1) ≤ l.endpoint := by
      simpa only [Layout.pointer_succ, Layout.capacity] using hnext
    have hready : ScanReady w rs (y.set dst (y.regs heap)) :=
      ⟨by simpa +decide using hyr.len,
       by simpa +decide using hyr.constants,
       by simpa +decide [hyr.keys] using hykeys,
       by simpa +decide [hyr.counts] using hycounts,
       fun p hp => hfit.of_le ((hkeys p hp).1.trans (by omega)),
       fun p hp => by simpa +decide [hyr.magnitude] using
         (hkeys p hp).2.trans (Nat.le_mul_of_pos_left U Nat.two_pos),
       fun p hp => hfit.of_le (by have := (hkeys p hp).1; omega),
       by simpa +decide [hyr.magnitude] using hfit.of_le hlabel,
       hfit.of_le hsmall,
       by simpa +decide [hyr.keys] using
         hfit.of_le (show 1 + 2 * l.n + rs.length ≤ budget l U by omega),
       by simpa +decide [hyr.counts] using
         hfit.of_le (show 1 + 3 * l.n + rs.length ≤ budget l U by omega),
       by simpa +decide [hyheap] using
         hfit.of_le (show l.pointer (y.regs current) + rs.length + 1 ≤ budget l U by omega),
       by simpa +decide [hyr.keys, hyheap] using
         (show 1 + 2 * l.n + rs.length ≤ l.pointer (y.regs current) by omega),
       by simpa +decide [hyr.counts, hyheap] using
         (show 1 + 3 * l.n + rs.length ≤ l.pointer (y.regs current) by omega)⟩
    obtain ⟨z, hz, hzi, hzh, hzd0, hzd1, hzp, hzf⟩ := body_exec
      (j := y.regs current) y rs hready hyr.magnitude hyr.digits
      (by simpa only [Layout.splits] using hyr.splits) rfl
      (by rw [hyr.capacity]; dsimp [Layout.capacity]; omega)
      (by rw [hyr.descriptors, hyheap]; exact l.descriptor_before hj _)
      (hfit.of_le (by
        rw [hyr.descriptors]
        have := l.descriptor_before hj 0
        have hp0 : l.pointer 0 ≤ l.endpoint := l.pointer_mono (i := 0) (j := l.arrays) (by omega)
        omega))
      (by rw [hyheap, hyr.capacity, ← Layout.pointer_succ]; exact hfit.of_le (hnext.trans he))
      (hfit.of_le (by omega))
    simp only [hyr.descriptors, hyheap, hyr.capacity] at hzd0 hzd1 hzp hzf hzh
    have hf (b : ℕ) (houtside : b < l.pointer (y.regs current) ∨
        l.pointer (y.regs current + 1) ≤ b)
        (hb0 : b ≠ l.descriptors + 2 * y.regs current)
        (hb1 : b ≠ l.descriptors + 2 * y.regs current + 1) : z.mem b = y.mem b :=
      hzf b (by simpa only [Layout.pointer_succ] using houtside) hb0 hb1
    have hview : Set.EqOn z.mem y.mem {b | (b < l.pointer (y.regs current) ∨
        l.pointer (y.regs current + 1) ≤ b) ∧ b ≠ l.descriptors + 2 * y.regs current ∧
        b ≠ l.descriptors + 2 * y.regs current + 1} :=
      fun {_} hb => hf _ hb.1 hb.2.1 hb.2.2
    have hdescbase : l.descriptors = 1 + 4 * l.n := rfl
    refine ⟨z, hz, ⟨hyr.transfer (fun i hi => hz.regs_eq hi), Layout.pointer_succ _ _ ▸ hzh,
      fun i hi => ?_, ?_, ?_, ?_⟩, hzi⟩
    · obtain rfl | hij := eq_or_ne i (y.regs current)
      · exact ⟨hzd0, hzd1, hzp⟩
      · have hi' : i < y.regs current := by omega
        obtain ⟨h0, h1, hp⟩ := hyout i hi'
        have hbefore := l.descriptor_before (hi'.trans hj) (y.regs current)
        refine ⟨(hf _ (.inl (by omega)) (by omega) (by omega)).trans h0,
          (hf _ (.inl (by omega)) (by omega) (by omega)).trans h1, ?_⟩
        have hlen' := (Math.length_array_le U l.digits rs i).trans
          (show rs.length + 1 ≤ l.capacity by dsimp [Layout.capacity]; omega)
        have hptr := l.pointer_mono (show i + 1 ≤ y.regs current by omega)
        rw [Layout.pointer_succ] at hptr
        have htable := l.descriptor_before hj i
        ram_keep hp using hview
    · ram_keep hykeys using hview
    · ram_keep hycounts using hview
    · intro b hnot
      have hb : b < l.descriptors ∨ l.endpoint ≤ b := by
        rw [Block.mem_footprint] at hnot
        dsimp only [Block.Owns] at hnot
        have := hbase.trans (l.pointer_mono (show 0 ≤ l.arrays by omega))
        omega
      have htable := l.descriptor_before hj (y.regs current)
      exact (hf b (by rcases hb with hb | hb <;> omega) (by omega) (by omega)).trans
        (hyframe b hnot)
  have hx : P (x.regs current) x :=
    ⟨hr, by simpa only [hidx] using hheap, fun i hi => absurd hi (by omega), hk, hc,
      Modifies.refl _ _⟩
  obtain ⟨y, hy, ⟨hyr, hyheap, hyout, hykeys, hycounts, hyframe⟩, hend⟩ :=
    ExecWithin.loop_count P (fun y hy => hy.1.arrays) hbody (by rw [hidx]; omega) hx
  refine ⟨y, ?_, fun j hj => hyout j (by omega), hend, ?_, hyr, hykeys, hycounts, hyframe⟩
  · simpa only [hidx, Nat.sub_zero, Nat.mul_comm] using hy
  · simpa only [Layout.endpoint] using hyheap

/-- Complete array/descriptor construction, including all native constant and layout setup. -/
theorem exec {w U : ℕ} (l : Layout) (rs : List (ℕ × ℕ)) (x : Data 48)
    (hU : x.regs Select.magnitude = U) (hn : x.regs inputLen = l.n)
    (hΛ : x.regs digits = l.digits) (hkreg : x.regs Scan.keys = 1 + 2 * l.n)
    (hcreg : x.regs Scan.counts = 1 + 3 * l.n) (hlenreg : x.regs len = rs.length)
    (hd : x.regs descriptors = l.descriptors) (hlen : rs.length ≤ l.n)
    (hk : Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) x.mem)
    (hc : Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) x.mem)
    (hkeys : ∀ p ∈ rs, p.1 ≤ 2 * U + 1 ∧ p.1 / 2 ≤ U)
    (hfit : Fits w (budget l U)) :
    ∃ y, ExecWithin w program x y (l.arrays * (43 * rs.length + 32) + 21) ∧
      Output l U rs y.mem ∧ Registers l U rs.length y ∧ y.regs heap = l.endpoint ∧
      Block.HoldsList (1 + 2 * l.n) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * l.n) (rs.map Prod.snd) y.mem ∧
      Modifies (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint x.mem y.mem := by
  obtain ⟨a, ha, har, hai, hah, ham⟩ := setup_exec l rs.length x hU hn hΛ hkreg hcreg
    hlenreg hd hfit
  obtain ⟨y, hy, hout, _, hyh, hyr, hykeys, hycounts, hyframe⟩ := loop_exec l rs a har hai hah
    hlen (by simpa only [ham] using hk) (by simpa only [ham] using hc) hkeys hfit
  exact ⟨y, (ha.seq hy).mono (by omega), hout, hyr, hyh, hykeys, hycounts,
    by simpa only [ham] using hyframe⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend.Arrays
