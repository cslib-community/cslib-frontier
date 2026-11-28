/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.QueryScan
import CslibFrontier.Computability.WordRAM.Record
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Tactic.UpdateSimp

/-!
# Native residue-class query lists

The fixed program calls `QueryScan.program` for each residue, storing the computed class count
and its row-major coordinate pairs. Each class receives a disjoint block of capacity `2n²`.
The cost of scanning once per residue is included; no class table is supplied as input.

This adapts the class builder in the pinned
[Theorem 17 program](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).

## Main definitions

* `Classes.program`: fixed twenty-register class enumeration.

## Main results

* `Classes.exec`: actual execution, class counts, coordinate readback and a memory frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Classes

open Cslib.WordRAM

/-- Source residue matrix. -/
abbrev src : Fin 20 := 0
/-- Query-scanner output pointer. -/
abbrev dst : Fin 20 := 1
/-- Matrix side. -/
abbrev size : Fin 20 := 2
/-- Query-scanner selected residue. -/
abbrev residue : Fin 20 := 3
/-- Query-scanner emitted count. -/
abbrev count : Fin 20 := 6
/-- Array of class counts. -/
abbrev counts : Fin 20 := 12
/-- Array of disjoint query blocks. -/
abbrev queries : Fin 20 := 13
/-- Number of residues to enumerate. -/
abbrev modulus : Fin 20 := 14
/-- Current class. -/
abbrev cursor : Fin 20 := 15
/-- Constant one. -/
abbrev one : Fin 20 := 16
/-- Count address. -/
abbrev addr : Fin 20 := 17
/-- Capacity in words of a query block. -/
abbrev stride : Fin 20 := 18

private abbrev scanReg : Fin 12 → Fin 20 := Fin.castLE (by decide)

private theorem scanReg_injective : Function.Injective scanReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 20 => k.val) h)

/-- Reuse the certified scanner with a disjoint register bank for the outer loop. -/
def scan : Code .standard 20 := QueryScan.program.rename (Fin.castLE (by decide))

/-- Compute the class's output pointer, scan, record its count, and advance. -/
def body : Code .standard 20 :=
  .seq (ram[ dst ← cursor * stride; dst ← dst + queries; residue ← cursor ])
    (.seq scan (ram[ addr ← counts + cursor; *addr ← count; cursor ← cursor + one ]))

/-- The modulus is runtime data; the program itself is independent of it. -/
def program : Code .standard 20 :=
  .seq (ram[ one ← #1; cursor ← #0; stride ← size * size; stride ← stride + stride ])
    (.loop (.lt cursor modulus) body)

/-- Fixed instruction graph, with no physical-width reads. -/
theorem program_fixed : program.size ≤ 64 ∧ ¬program.ReadsWidth := by decide

private theorem body_preserves : ∀ i : Fin 20,
    (i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus ∨ i = one ∨ i = stride) →
      body.Preserves i := by decide

/-- Enumerate every residue class into actual count and coordinate arrays. The source matrix,
count array and query capacity blocks must occur in that order. The final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 20) (R : ℕ → ℕ) (h1 : Fits w 1)
    (hinput : ∀ q < x.regs size * x.regs size, x.mem (x.regs src + q) = R q)
    (hsource : x.regs src + x.regs size * x.regs size ≤ x.regs counts)
    (hblocks : x.regs counts + x.regs modulus ≤ x.regs queries)
    (hcount : Fits w (x.regs counts + x.regs modulus))
    (hquery : Fits w (x.regs queries + 2 * (x.regs size * x.regs size) * x.regs modulus))
    (harea : Fits w (2 * (x.regs size * x.regs size))) :
    ∃ y, ExecWithin w program x y
        (x.regs modulus * (14 * (x.regs size * x.regs size) + 14) + 6) ∧
      y.regs cursor = x.regs modulus ∧
      (∀ j < x.regs modulus,
        y.mem (x.regs counts + j) = Nat.count (fun q => R q = j)
          (x.regs size * x.regs size)) ∧
      (∀ j < x.regs modulus, ∀ q < x.regs size * x.regs size, R q = j →
        y.mem (x.regs queries + 2 * (x.regs size * x.regs size) * j +
          2 * Nat.count (fun k => R k = j) q) = q / x.regs size ∧
        y.mem (x.regs queries + 2 * (x.regs size * x.regs size) * j +
          2 * Nat.count (fun k => R k = j) q + 1) = q % x.regs size) ∧
      (∀ a, ¬(x.regs counts ≤ a ∧ a < x.regs counts + x.regs modulus) →
        ¬(x.regs queries ≤ a ∧
          a < x.regs queries + 2 * (x.regs size * x.regs size) * x.regs modulus) →
        y.mem a = x.mem a) := by
  let n := x.regs size
  let p := x.regs modulus
  let b := x.regs counts
  let d := x.regs queries
  let s := 2 * (n * n)
  let C (j q : ℕ) := Nat.count (fun k => R k = j) q
  change x.regs src + n * n ≤ b at hsource
  change b + p ≤ d at hblocks
  change Fits w (b + p) at hcount
  change Fits w (d + s * p) at hquery
  change Fits w s at harea
  let I (y : Data 20) : Prop :=
    (∀ i, i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus →
      y.regs i = x.regs i) ∧
      y.regs one = 1 ∧ y.regs stride = s ∧ y.regs cursor ≤ p ∧
      (∀ j < y.regs cursor, y.mem (b + j) = C j (n * n)) ∧
      (∀ j < y.regs cursor, ∀ q < n * n, R q = j →
        y.mem (d + s * j + 2 * C j q) = q / n ∧
        y.mem (d + s * j + 2 * C j q + 1) = q % n) ∧
      (∀ a, ¬(b ≤ a ∧ a < b + y.regs cursor) →
        ¬(d ≤ a ∧ a < d + s * y.regs cursor) → y.mem a = x.mem a)
  have hbody (y : Data 20) (hy : I y) (hc : (Cond.lt cursor modulus).Holds y) :
      ∃ z, ExecWithin w body y z (14 * (n * n) + 12) ∧ I z ∧
        p - z.regs cursor < p - y.regs cursor := by
    obtain ⟨hyr, hyo, hys, hyc, hycounts, hypairs, hyframe⟩ := hy
    have hyn : y.regs size = n := hyr size (by simp)
    have hyp : y.regs modulus = p := hyr modulus (by simp)
    have hyb : y.regs counts = b := hyr counts (by simp)
    have hyd : y.regs queries = d := hyr queries (by simp)
    have hysrc : y.regs src = x.regs src := hyr src (by simp)
    have hlt : y.regs cursor < p := by simpa only [Cond.holds_lt, hyp] using hc
    let j := y.regs cursor
    change j < p at hlt
    have hmul : s * (j + 1) ≤ s * p := Nat.mul_le_mul_left s hlt
    have hstep : s * (j + 1) = s * j + s := Nat.mul_succ s j
    have hsj : j * s ≤ s * p := by rw [Nat.mul_comm j s]; omega
    have hexec : ∃ z, ExecWithin w body y z (14 * (n * n) + 12) ∧
        z.regs cursor = j + 1 ∧
        (∀ q, ¬(d + s * j ≤ q ∧ q < d + s * (j + 1)) →
          z.mem q = Function.update y.mem (b + j) (C j (n * n)) q) ∧
        (∀ q < n * n, R q = j →
          z.mem (d + s * j + 2 * C j q) = q / n ∧
          z.mem (d + s * j + 2 * C j q + 1) = q % n) ∧
        (∀ i, (i = src ∨ i = size ∨ i = counts ∨ i = queries ∨ i = modulus ∨
          i = one ∨ i = stride) → z.regs i = y.regs i) := by
      refine WP.exists_execWithin_preserves (fun i hi => body_preserves i hi) ?_
      wram_exec [body, scan, hys, hyd]
      have hread : ∀ q < n * n, y.mem (x.regs src + q) = R q := fun q hq => by
        rw [hyframe _ (by dsimp [b, n] at *; omega) (by dsimp [d, b, n] at *; omega)]
        exact hinput q hq
      have hyn' : ∀ h, y.regs (Fin.castLE h QueryScan.size) = n := fun _ => hyn
      have hysrc' : ∀ h, y.regs (Fin.castLE h QueryScan.src) = x.regs src := fun _ => hysrc
      wram_call (QueryScan.exec _ R h1
        (by wram_simp [hysrc', hyn']; exact hread)
        (by wram_simp [hysrc', hyn']; exact hcount.of_le (by dsimp [b, n] at *; omega))
        (by
          wram_simp [hyn']
          exact hquery.of_le (by dsimp [j, s] at *; rw [Nat.mul_comm _ (2 * (n * n))]; omega))
        (by wram_simp [hysrc', hyn']; dsimp [j, s, b, d, n] at *; omega))
        canonical scanReg_injective with v ⟨-, hvc, -, hvpairs, hvframe⟩
      wram_simp [hyn'] at hvc hvpairs hvframe
      have hv' : v.regs QueryScan.count = C j (n * n) := hvc
      wram_exec [hv', hyb, hyo]
      refine ⟨by wram_simp [hyn']; omega, fun hpres => ⟨by wram_simp; rfl, ?_, ?_, hpres⟩⟩
      · intro q hq
        change Function.update v.mem (b + j) (C j (n * n)) q =
          Function.update y.mem (b + j) (C j (n * n)) q
        by_cases hqb : q = b + j
        · rw [hqb, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hqb, Function.update_of_ne hqb]
          apply hvframe q
          rw [hv', Nat.mul_comm (y.regs cursor) s, Nat.add_comm (s * y.regs cursor) d]
          have : C j (n * n) ≤ n * n := Nat.count_le _
          dsimp [s, j] at *; omega
      · intro q hq hkey
        have hrank : C j q < n * n := (Nat.count_le _).trans_lt hq
        have hcountaddr : b + j < d := by dsimp [b, d, p, j] at *; omega
        obtain ⟨hp1, hp2⟩ := hvpairs q hq hkey
        rw [Nat.mul_comm (y.regs cursor) s, Nat.add_comm (s * y.regs cursor) d] at hp1 hp2
        change Function.update v.mem (b + j) (C j (n * n)) (d + s * j + 2 * C j q) = q / n ∧
          Function.update v.mem (b + j) (C j (n * n)) (d + s * j + 2 * C j q + 1) = q % n
        exact ⟨by rw [Function.update_of_ne (by omega)]; exact hp1,
          by rw [Function.update_of_ne (by omega)]; exact hp2⟩
    obtain ⟨z, hcost, hzj, hzframe, hzpairs, hpres⟩ := hexec
    refine ⟨z, hcost, ⟨?_, (hpres one (by simp)).trans hyo, (hpres stride (by simp)).trans hys,
      by omega, ?_, ?_, ?_⟩, by omega⟩
    · intro i hi
      exact (hpres i (by rcases hi with h | h | h | h | h <;> simp [h])).trans (hyr i hi)
    · intro k hk; rw [hzj] at hk
      rw [hzframe _ (by dsimp [b, d, p] at *; omega)]
      by_cases hkj : k = j
      · rw [hkj]; update_simp
      · update_simp; exact hycounts k (by omega)
    · intro k hk q hq hkey; rw [hzj] at hk
      have hrank : C k q < n * n := (Nat.count_le _).trans_lt hq
      have hcountaddr : b + j < d := by dsimp [b, d, p] at *; omega
      by_cases hkj : k = j
      · rw [hkj] at hkey ⊢; exact hzpairs q hq hkey
      · have hmul' : s * (k + 1) ≤ s * j := Nat.mul_le_mul_left s (by omega)
        have hstep' : s * (k + 1) = s * k + s := Nat.mul_succ s k
        have hsep : ¬(d + s * j ≤ d + s * k + 2 * C k q ∧
            d + s * k + 2 * C k q < d + s * (j + 1)) := by dsimp [s] at *; omega
        have hsep1 : ¬(d + s * j ≤ d + s * k + 2 * C k q + 1 ∧
            d + s * k + 2 * C k q + 1 < d + s * (j + 1)) := by dsimp [s] at *; omega
        rw [hzframe _ hsep, hzframe _ hsep1]
        obtain ⟨hp1, hp2⟩ := hypairs k (by omega) q hq hkey
        exact ⟨by update_simp; exact hp1, by update_simp; exact hp2⟩
    · intro q hqb hqd; rw [hzj] at hqb hqd
      rw [hzframe q (by dsimp [j] at *; omega)]; update_simp
      exact hyframe q (by dsimp [j] at *; omega) (by
        dsimp [j] at *
        have := Nat.mul_le_mul_left s (show y.regs cursor ≤ y.regs cursor + 1 by omega)
        omega)
  refine WP.exists_execWithin ?_
  wram_exec [program]
  wram_call (ExecWithin.loop_invariant I (fun y => p - y.regs cursor) hbody
    ⟨fun i hi => by rcases hi with rfl | rfl | rfl | rfl | rfl <;> wram_simp,
     by wram_simp, by wram_simp [s, n]; omega, by wram_simp; exact Nat.zero_le _,
     fun _ hj => by wram_simp at hj, fun _ hj => by wram_simp at hj, fun _ _ _ => rfl⟩)
    with y ⟨⟨hyr, -, -, hyc, hycounts, hypairs, hyframe⟩, hc⟩
  have hyp : y.regs modulus = p := hyr modulus (by simp)
  have hend : y.regs cursor = p := by simp only [Cond.holds_lt, hyp] at hc; omega
  refine ⟨by wram_simp; simp only [Nat.add_assoc, Nat.reduceAdd]; dsimp [n, p]; omega,
    hend, by simpa only [hend] using hycounts,
    by simpa only [hend] using hypairs, by simpa only [hend] using hyframe⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.Classes
