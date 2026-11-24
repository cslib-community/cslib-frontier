/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Foundations.Data.Nat.HalvingRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# A charged native integer `k`-th root

The `k`-th root `Nat.nthRoot k n`, the largest `a` with `a ^ k ≤ n`, is found by binary search on
`[0, n + 1)`. Each probe compares `m ^ k` with `n` by a *capped power*: repeated multiplication
that stops as soon as the partial product exceeds `n`, so every product stays below `n (n + 1)`
and fits a word of about twice the bit length of `n`. The search halves the interval, so it makes
at most `⌈log₂ (n + 1)⌉` probes.

## Main definitions

* `NatNthRoot.CapPow.program`: compare `m ^ k` with a bound `n` by capped multiplication.
* `NatNthRoot.program`: binary search for `Nat.nthRoot k n`.

## Main results

* `NatNthRoot.CapPow.exec`: within `6 k + 5` instructions, the capped power is at most `n`
  exactly when `m ^ k ≤ n`, and then equals `m ^ k`.
* `NatNthRoot.exec`: `Nat.nthRoot k n` within `⌈log₂ (n + 1)⌉ (6 k + 13) + 7` instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatNthRoot

open Cslib.WordRAM

namespace CapPow

/-- Base, preserved. -/
abbrev m : Fin 6 := 0
/-- Exponent, preserved. -/
abbrev k : Fin 6 := 1
/-- Bound, preserved. -/
abbrev n : Fin 6 := 2
/-- Capped power, the output. -/
abbrev p : Fin 6 := 3
/-- Counter. -/
abbrev i : Fin 6 := 4
/-- Constant one. -/
abbrev one : Fin 6 := 5

/-- Stop once the partial product exceeds the bound; otherwise multiply once more. -/
def body : Code .standard 6 :=
  ram[ if n < p then [ i ← k ] else [ p ← p * m; i ← i + one ] ]

/-- Capped repeated multiplication. -/
def program : Code .standard 6 :=
  .seq (ram[ p ← #1; i ← #0; one ← #1 ]) (.loop (.lt i k) body)

/-- For a positive base, the capped power is at most the bound exactly when the true power is,
and then the two agree. The products stay below `n m`. -/
theorem exec {w : ℕ} (x : Data 6) (hm : 1 ≤ x.regs m) (h1 : Fits w 1)
    (hk : Fits w (x.regs k)) (hprod : Fits w (x.regs n * x.regs m)) :
    ∃ y, ExecWithin w program x y (6 * x.regs k + 5) ∧
      (y.regs p ≤ x.regs n ↔ x.regs m ^ x.regs k ≤ x.regs n) ∧
      (x.regs m ^ x.regs k ≤ x.regs n → y.regs p = x.regs m ^ x.regs k) ∧
      y.regs m = x.regs m ∧ y.regs k = x.regs k ∧ y.regs n = x.regs n ∧
      y.regs one = 1 ∧ y.mem = x.mem := by
  set b := x.regs m
  set e := x.regs k
  set N := x.regs n
  wram_exec [program]
  let I (y : Data 6) : Prop := y.regs m = b ∧ y.regs k = e ∧ y.regs n = N ∧ y.regs one = 1 ∧
    y.regs i ≤ e ∧ (y.regs p = b ^ y.regs i ∨ (N < y.regs p ∧ N < b ^ e)) ∧ y.mem = x.mem
  refine WP.of_spec (ExecWithin.loop_invariant (T := 4) I (fun y => e - y.regs i) ?_ ?_) ?_
  · rintro y ⟨hym, hyk, hyn, hyo, hyi, hyp, hymem⟩ hc
    have hlt : y.regs i < e := by simpa only [Cond.holds_lt, hyk] using hc
    unfold body
    by_cases hover : N < y.regs p
    · wram_exec [hyn, hyk, hover]
      dsimp only [I]
      wram_simp [hym, hyk, hyn, hyo, hymem, le_rfl]
      refine ⟨Or.inr ⟨hover, ?_⟩, by omega⟩
      exact hyp.elim (fun h => hover.trans_le (h ▸ Nat.pow_le_pow_right hm hyi)) And.right
    · have hpow : y.regs p = b ^ y.regs i := hyp.resolve_right fun h => hover h.1
      have hmul : Fits w (y.regs p * b) := by
        fits [Nat.mul_le_mul_right b (show y.regs p ≤ N by omega)]
      wram_exec [hyn, hym, hyo, hover, hmul]
      dsimp only [I]
      wram_simp [hym, hyk, hyn, hyo, hymem, hpow, ← pow_succ]
      exact ⟨⟨by omega, Or.inl trivial⟩, by omega⟩
  · dsimp only [I, b, e, N]; wram_simp; simp
  · rintro y ⟨⟨hym, hyk, hyn, hyo, hyi, hyp, hymem⟩, hc⟩
    have hend : y.regs i = e := by simp only [Cond.holds_lt, hyk] at hc; omega
    rw [hend] at hyp
    refine ⟨by wram_simp; omega, ?_, ?_, hym, hyk, hyn, hyo, hymem⟩
    · exact hyp.elim (fun h => by rw [h]) fun h => ⟨by omega, by omega⟩
    · exact fun hle => hyp.resolve_right fun h => by omega

/-- Run the capped power on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 6 → Fin r) (hf : f.Injective) (x : Data r)
    (hm : 1 ≤ x.regs (f m)) (h1 : Fits w 1) (hk : Fits w (x.regs (f k)))
    (hprod : Fits w (x.regs (f n) * x.regs (f m))) :
    ∃ y, ExecWithin w (program.rename f) x y (6 * x.regs (f k) + 5) ∧
      (y.regs (f p) ≤ x.regs (f n) ↔ x.regs (f m) ^ x.regs (f k) ≤ x.regs (f n)) ∧
      (x.regs (f m) ^ x.regs (f k) ≤ x.regs (f n) →
        y.regs (f p) = x.regs (f m) ^ x.regs (f k)) ∧
      y.regs (f m) = x.regs (f m) ∧ y.regs (f k) = x.regs (f k) ∧
      y.regs (f n) = x.regs (f n) ∧ y.regs (f one) = 1 ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) hm h1 hk hprod)
  exact ⟨y, hy, hpost⟩

end CapPow

/-- Bound `n`, preserved. -/
abbrev n : Fin 10 := 0
/-- Root degree `k`, preserved. -/
abbrev k : Fin 10 := 1
/-- Lower end of the search interval, and the output. -/
abbrev lo : Fin 10 := 2
/-- Upper end of the search interval. -/
abbrev hi : Fin 10 := 3
/-- Probe. -/
abbrev mid : Fin 10 := 4
/-- Capped power of the probe. -/
abbrev p : Fin 10 := 5
/-- Counter of the capped power. -/
abbrev i : Fin 10 := 6
/-- Constant one. -/
abbrev one : Fin 10 := 7
/-- Constant two. -/
abbrev two : Fin 10 := 8
/-- `lo + 1`, for the loop test. -/
abbrev t : Fin 10 := 9

/-- The registers of the capped power inside the search. -/
def capMap : Fin 6 → Fin 10 := ![mid, k, n, p, i, one]

theorem capMap_injective : capMap.Injective := by decide

/-- One probe: halve the interval according to the capped power of its midpoint. -/
def body : Code .standard 10 :=
  .seq (ram[ mid ← lo + hi; mid ← mid / two ]) (.seq (CapPow.program.rename capMap)
    (ram[ if n < p then [ hi ← mid ] else [ lo ← mid ]; t ← lo + one ]))

/-- Binary search for the `k`-th root on `[0, n + 1)`. -/
def program : Code .standard 10 :=
  .seq (ram[ lo ← #0; one ← #1; two ← #2; hi ← n + one; t ← lo + one ]) (.loop (.lt t hi) body)

/-- Compute `Nat.nthRoot k n` for `k ≥ 1` within `⌈log₂ (n + 1)⌉ (6 k + 13) + 7` instructions,
preserving `n`, `k` and memory. Products and search bounds are at most `n² + 2 n + 1`, but the
probe counters run up to `k` whatever `n` is, hence the separate hypothesis `hkfit`. -/
theorem exec {w : ℕ} (x : Data 10) (hk : 1 ≤ x.regs k) (hkfit : Fits w (x.regs k))
    (hfit : Fits w (x.regs n * x.regs n + 2 * x.regs n + 2)) :
    ∃ y, ExecWithin w program x y (Nat.clog 2 (x.regs n + 1) * (6 * x.regs k + 13) + 7) ∧
      y.regs lo = Nat.nthRoot (x.regs k) (x.regs n) ∧ y.regs n = x.regs n ∧
      y.regs k = x.regs k ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.mem = x.mem := by
  set N := x.regs n
  set e := x.regs k
  have he0 : e ≠ 0 := by omega
  have h1 : Fits w 1 := by fits
  have hn1 : Fits w (N + 1) := by fits [show N + 1 ≤ N * N + 2 * N + 2 by nlinarith]
  wram_exec [program]
  let I (y : Data 10) : Prop := y.regs n = N ∧ y.regs k = e ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs t = y.regs lo + 1 ∧ y.regs lo < y.regs hi ∧ y.regs hi ≤ N + 1 ∧
    y.regs lo ^ e ≤ N ∧ N < y.regs hi ^ e ∧ y.mem = x.mem
  refine WP.of_spec
    (ExecWithin.loop_invariant (T := 6 * e + 11) I
      (fun y => Nat.clog 2 (y.regs hi - y.regs lo)) ?_ ?_) ?_
  · rintro y ⟨hyn, hyk, hyo, hyt2, hyt, hlohi, hhi, hlo, hhip, hymem⟩ hc
    obtain ⟨l, hl⟩ : ∃ l, y.regs lo = l := ⟨_, rfl⟩
    obtain ⟨h, hh⟩ : ∃ h, y.regs hi = h := ⟨_, rfl⟩
    simp only [hl, hh] at hlohi hlo hhip hyt hhi
    have hgap : l + 1 < h := by simpa only [Cond.holds_lt, hyt, hh] using hc
    have hsum : Fits w (l + h) := by fits [show l + h ≤ N * N + 2 * N + 2 by nlinarith]
    have hprod_mid : Fits w (N * ((l + h) / 2)) := by
      fits [show N * ((l + h) / 2) ≤ N * N + 2 * N + 2 from
        (Nat.mul_le_mul_left N (by omega : (l + h) / 2 ≤ N)).trans (by omega)]
    unfold body
    generalize hsub : CapPow.program.rename capMap = sub
    wram_exec [hl, hh, hyt2]
    subst hsub
    refine WP.of_spec (ExecWithin.rename_post capMap_injective (CapPow.exec _ ?_ h1 ?_ ?_)) ?_
    · rw [Data.comap_regs, show capMap CapPow.m = mid from rfl]; wram_simp; omega
    · rw [Data.comap_regs, show capMap CapPow.k = k from rfl]; wram_simp [hyk]; exact hkfit
    · rw [Data.comap_regs, Data.comap_regs, show capMap CapPow.n = n from rfl,
        show capMap CapPow.m = mid from rfl]
      wram_simp [hyn]; exact hprod_mid
    rintro y₂ ⟨⟨hple, -, hy₂m, hy₂k, hy₂n, hy₂o, hy₂mem⟩, hframe⟩
    simp only [Data.comap_regs, Data.comap_mem, show capMap CapPow.m = mid from rfl,
      show capMap CapPow.k = k from rfl, show capMap CapPow.n = n from rfl,
      show capMap CapPow.p = p from rfl, show capMap CapPow.one = one from rfl]
      at hple hy₂m hy₂k hy₂n hy₂o hy₂mem ⊢
    wram_simp [hyn, hyk] at hple hy₂m hy₂k hy₂n hy₂o hy₂mem ⊢
    have hy₂lo : y₂.regs lo = l := by regs_frame
    have hy₂hi : y₂.regs hi = h := by regs_frame
    have hy₂two : y₂.regs two = 2 := by regs_frame
    have hl1 : Fits w (l + 1) := by fits [show l + 1 ≤ l + h by omega]
    have hm1 : Fits w ((l + h) / 2 + 1) := by fits [show (l + h) / 2 + 1 ≤ l + h by omega]
    wram_exec [hy₂n, hy₂o, hy₂m, hy₂lo, hy₂hi]
    · have hpow : N < ((l + h) / 2) ^ e := by
        by_contra hle; exact absurd (hple.mpr (not_lt.mp hle)) (not_le.mpr hc)
      dsimp only [I]
      wram_simp [hy₂n, hy₂k, hy₂o, hy₂two, hy₂lo, hy₂mem, hymem]
      exact ⟨⟨by omega, by omega, hlo, hpow⟩,
        Nat.clog_two_lt_clog_two_of_le_half (by omega) (by omega)⟩
    · have hpow : ((l + h) / 2) ^ e ≤ N := hple.mp (not_lt.mp hc)
      dsimp only [I]
      wram_simp [hy₂n, hy₂k, hy₂o, hy₂two, hy₂hi, hy₂mem, hymem]
      exact ⟨⟨by omega, hhi, hpow, hhip⟩,
        Nat.clog_two_lt_clog_two_of_le_half (by omega) (by omega)⟩
  · dsimp only [I, N, e]
    wram_simp
    exact ⟨le_rfl, by simp [show x.regs k ≠ 0 from he0],
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_self_pow he0 _)⟩
  · rintro y ⟨⟨hyn, hyk, hyo, hytwo, hyt, hlohi, -, hlo, hhip, hymem⟩, hc⟩
    have hhi : y.regs hi = y.regs lo + 1 := by simp only [Cond.holds_lt, hyt] at hc; omega
    rw [hhi] at hhip
    refine ⟨?_, (Nat.nthRoot_eq_of_le_of_lt hlo hhip).symm, hyn, hyk, hyo, hytwo, hymem⟩
    wram_simp
    dsimp only [N, e]
    exact le_rfl

/-- Run the binary search on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 10 → Fin r) (hf : f.Injective) (x : Data r)
    (hk : 1 ≤ x.regs (f k)) (hkfit : Fits w (x.regs (f k)))
    (hfit : Fits w (x.regs (f n) * x.regs (f n) + 2 * x.regs (f n) + 2)) :
    ∃ y, ExecWithin w (program.rename f) x y
        (Nat.clog 2 (x.regs (f n) + 1) * (6 * x.regs (f k) + 13) + 7) ∧
      y.regs (f lo) = Nat.nthRoot (x.regs (f k)) (x.regs (f n)) ∧
      y.regs (f n) = x.regs (f n) ∧ y.regs (f k) = x.regs (f k) ∧
      y.regs (f one) = 1 ∧ y.regs (f two) = 2 ∧ y.mem = x.mem := by
  obtain ⟨y, hy, hpost, -⟩ := ExecWithin.rename_post hf (exec (x.comap f) hk hkfit hfit)
  exact ⟨y, hy, hpost⟩

end Cslib.Algorithms.WordRAM.NatNthRoot
