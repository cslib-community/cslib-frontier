/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Estimate
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Schedule
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The errors of a call of the certificate procedure

The configuration of Algorithm 1 used by [Khanna, Putterman and Song][KhannaPuttermanSong2026]
(§3.4–§3.5) and the bound on the errors of one call (§3.6, "Bounding the number of errors",
p. 23). These are steps in the proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325), not results
of their own.

`Cslib.Query.Certificate.Config.derandomized γ hγ msfSub` runs Algorithm 1 with the parameter
`γ > 0`, the schedule of Lemma 3.11 (`Cslib.Query.Certificate.schedule`), the estimator of §3.5
(`Cslib.Query.Certificate.estimator`) and a given exact minimum spanning forest subroutine.

An error of an edge in a call (p. 17, `Cslib.Query.Certificate.errors`) is a bad scheduled round or
a wrong estimate. By Lemmas 3.10 and 3.11 the first kind number at most
`(7 t² √(m n) + 2m / t) / log 2`, and by §3.5 the second at most `m / t`; since `log 2 > 0.69`, a
call on `n` vertices and `m` edges with `t = γ d³` has at most `11 t² √(m n) + 4m / t` errors
(`Cslib.Query.Certificate.card_errors_le`). The paper states `O(t² √(m n)) + 4m / t`.

## Main definitions

* `Cslib.Query.Certificate.Config.derandomized`.

## Main results

* `Cslib.Query.Certificate.card_errors_le`: at most `11 t² √(m n) + 4m / t` errors per call.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.4–§3.6, pp. 18–23.
-/

public section

namespace Cslib.Query.Certificate

open Finset

variable {V E W : Type} [DecidableEq V] [DecidableEq E]

/-- **The derandomized configuration** of Algorithm 1 (§3.4–§3.5): the parameter `γ > 0`, the
schedule of Lemma 3.11, the estimator of §3.5, and the exact minimum spanning forest subroutine
`msfSub`. -/
@[expose, simps] noncomputable def Config.derandomized (γ : ℕ) (hγ : 0 < γ)
    (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) : Config V E where
  γ := γ
  sched := schedule γ hγ
  est := estimator γ
  msfSub := msfSub

variable [LinearOrder W]

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the errors of a call
(§3.6, "Bounding the number of errors", p. 23). For the derandomized configuration with a correct
exact minimum spanning forest subroutine, injective weights and a well-formed instance on `n`
vertices and `m` edges at level `d`, with `t = γ d³`, at most `11 t² √(m n) + 4m / t` edges have an
error in the call. -/
theorem card_errors_le (γ : ℕ) (hγ : 0 < γ)
    (msfSub : (E → Sym2 V) → Finset E → FreeM (LEQuery E) (Finset E)) {w : E → W}
    (hw : Function.Injective w) (hmsf : (Config.derandomized γ hγ msfSub).ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    (#(errors (Config.derandomized γ hγ msfSub) w inst) : ℝ) ≤
      11 * (levelT γ inst.level : ℝ) ^ 2 * √(#inst.edges * #inst.vertices) +
        4 * #inst.edges / levelT γ inst.level := by
  classical
  set cfg := Config.derandomized (V := V) γ hγ msfSub
  set t := levelT γ inst.level
  set m := #inst.edges
  set n := #inst.vertices
  have hbad := card_badRound_schedule_mul_log_two_le hw hmsf hwf (cfg := cfg) hγ rfl
  have hhist := log_card_histories_le cfg.γ inst
  have hest := card_estimate_ne_prefSeq_le cfg w hw hmsf hwf hγ rfl
  set X := #{e ∈ inst.edges | BadRound t (prefSeq cfg w inst e) (cfg.sched inst e)}
  set Y := #{e ∈ inst.edges | estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
    prefSeq cfg w inst e (cfg.sched inst e)}
  have hsub : errors cfg w inst ⊆
      {e ∈ inst.edges | BadRound t (prefSeq cfg w inst e) (cfg.sched inst e)} ∪
        {e ∈ inst.edges | estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
          prefSeq cfg w inst e (cfg.sched inst e)} := by
    intro e he
    obtain ⟨heE, h⟩ := mem_errors.1 he
    rcases hasError_iff.1 h with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨heE, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨heE, h⟩)
  have hcard : (#(errors cfg w inst) : ℝ) ≤ X + Y := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have ht : (0 : ℝ) < t := by
    have : 0 < t := Nat.mul_pos hγ (pow_pos inst.level.pos 3)
    exact_mod_cast this
  have hlog := Real.log_two_gt_d9
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have ha : 0 ≤ 7 * (t : ℝ) ^ 2 * √(m * n) := by positivity
  have hb : 0 ≤ 2 * (m : ℝ) / t := by positivity
  -- the bad rounds: `X log 2 ≤ 7 t² √(m n) + 2m / t`
  have hX : (X : ℝ) * Real.log 2 ≤ 7 * (t : ℝ) ^ 2 * √(m * n) + 2 * m / t :=
    hbad.trans (add_le_add_left hhist _)
  have hX' : (X : ℝ) ≤ 11 / 7 * (7 * (t : ℝ) ^ 2 * √(m * n)) + 3 / 2 * (2 * m / t) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hY : (Y : ℝ) ≤ m / t := hest
  have : (m : ℝ) / t * 4 = 4 * m / t := by ring
  calc (#(errors cfg w inst) : ℝ) ≤ X + Y := hcard
    _ ≤ 11 / 7 * (7 * (t : ℝ) ^ 2 * √(m * n)) + 3 / 2 * (2 * m / t) + m / t := by linarith
    _ = 11 * (t : ℝ) ^ 2 * √(m * n) + 4 * m / t := by ring

end Cslib.Query.Certificate
