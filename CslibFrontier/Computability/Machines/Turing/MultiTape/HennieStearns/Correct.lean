/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Simulate
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The Hennie–Stearns theorem

A `k`-work-tape machine running in time `t` is simulated by the two-work-tape machine
`hennieStearns tm` in time `O(t log t)`: `hennieStearns_spec`, with the bound
`(80 k + 2) (t + 1) (log₂ (t + 1) + 1)`.

The machine represents each step of `tm` (`rep_step`) in time `1 + ∑ 80 · 2 ^ j` over the levels
`j` of the moves of the moving tracks. Along the run, the moves of each track have the levels of
a run of moves of a balanced track (`ZTrack.SameLen`), so by `ZTrack.cost_le` the levels of the
at most `t` moves of each track sum to at most `t (log₂ (t + 1) + 1)`.

## Main results

* `Turing.MultiTapeTM.hennieStearns_spec`: the simulation in time `O(t log t)`
  ([HennieStearns1966], Theorem 1, p. 541).

## References

* [F. C. Hennie and R. E. Stearns, *Two-tape simulation of multitape Turing
  machines*][HennieStearns1966]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open HennieStearns

variable {k : ℕ} {Symbol State : Type} (tm : MultiTapeTM k Symbol State)
  {x : List Symbol}

namespace HennieStearns

/-- The histories of the tracks after one more step. -/
def extend (mv : Fin k → SignType) (hist : Fin k → List Side) (i : Fin k) : List Side :=
  if mv i ≠ 0 then hist i ++ [ZTrack.sideOf (mv i)] else hist i

/-- **Reaching a running configuration.** After the `n`-th step of `tm`, while it runs, the
Hennie–Stearns machine represents it, the tracks having the zone lengths of runs of moves of a
blank track, within `1 + n + 80 ∑ cost` steps. -/
theorem reach (x : List Symbol) (n : ℕ) (hn : (tm.runFrom (tm.initCfg x) n).state ≠ none) :
    ∃ T Z J, ∃ hist : Fin k → List Side,
      Rep (tm.runFrom (tm.initCfg x) n) Z J
        ((hennieStearns tm).runFrom ((hennieStearns tm).initCfg (x.map Sum.inl)) T) ∧
      (∀ i, (hist i).length ≤ n) ∧
      (∀ i, ZTrack.SameLen (Z i) ((blankTrack (Symbol := Symbol)).run 0 (hist i))) ∧
      T ≤ 1 + n + ∑ i, 80 * (blankTrack (Symbol := Symbol)).cost 0 (hist i) := by
  induction n with
  | zero =>
    refine ⟨1, fun _ => blankTrack, 0, fun _ => [], rep_init tm x, fun _ => le_rfl,
      fun _ _ _ => rfl, by simp⟩
  | succ n ih =>
    have hn' : (tm.runFrom (tm.initCfg x) n).state ≠ none := by
      intro h
      apply hn
      rw [runFrom_succ, step_of_halt h, h]
    obtain ⟨T, Z, J, hist, hR, hlen, hsame, hT⟩ := ih hn'
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hn'
    rw [runFrom_succ] at hn ⊢
    set c := tm.runFrom (tm.initCfg x) n
    set a := tm.tr q c.inputSymbol c.workTapeSymbols
    obtain ⟨T', J', hT', hR'⟩ := rep_step tm hR hq hn
    rw [← runFrom_add] at hR'
    set mv := moves a
    set W := written a Z
    have hVW : ∀ i, (W i).Valid J := fun i => (hR.valid i).withCenter _
    have hVY : ∀ i, ((blankTrack (Symbol := Symbol)).run 0 (hist i)).Valid (hist i).length :=
      fun i => by simpa using blankTrack_valid.run (hist i)
    have htrig : ∀ i, (W i).trig J (srcSide mv i) =
        ((blankTrack (Symbol := Symbol)).run 0 (hist i)).trig (0 + (hist i).length)
          (ZTrack.sideOf (mv i)) := fun i => by
      rw [zero_add]
      exact ZTrack.trig_eq_of_sameLen (hVW i) (hVY i) (hsame i) _
    refine ⟨T + T', movedFrom mv 0 W J, J', extend mv hist, hR', fun i => ?_, fun i => ?_, ?_⟩
    · have := hlen i
      simp only [extend]
      split_ifs
      · rw [List.length_append, List.length_singleton]; omega
      · omega
    · simp only [movedFrom, extend, zero_le, true_and]
      split_ifs with hm
      · rw [ZTrack.run_append, zero_add]
        exact ZTrack.sameLen_move (hVW i) (hVY i) (hsame i) _
      · exact hsame i
    · have hcost : ∀ i, (blankTrack (Symbol := Symbol)).cost 0 (extend mv hist i) =
          (blankTrack (Symbol := Symbol)).cost 0 (hist i) +
            (if mv i ≠ 0 then 2 ^ (W i).trig J (srcSide mv i) else 0) := fun i => by
        simp only [extend]
        split_ifs
        · rw [ZTrack.cost_append, htrig]
        · rfl
      have hops : opsTime mv 0 W J =
          ∑ i, 80 * (if mv i ≠ 0 then 2 ^ (W i).trig J (srcSide mv i) else 0) := by
        simp only [opsTime, zero_le, true_and]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> rfl
      simp only [hcost, mul_add, Finset.sum_add_distrib]
      rw [← hops]
      omega

end HennieStearns

/-- **The Hennie–Stearns theorem** ([HennieStearns1966], Theorem 1, p. 541). If the `k`-work-tape
machine `tm` halts on `x` within `t` steps, then the two-work-tape machine `hennieStearns tm`
halts on `x` with the same output within `(80 k + 2) (t + 1) (log₂ (t + 1) + 1)` steps.

The source bounds the simulation of `n` steps by `a n log₂ n` for `n > 1`, with `a` independent of
`n`; the explicit bound here also covers `t ≤ 1`. **Deviation:** the simulator works over the
enlarged alphabet `Symbol ⊕ ACell ⊕ BCell` on all its tapes, so its input is `x.map Sum.inl` and
its output is `tm`'s mapped by `Sum.inl`, where the source enlarges only the storage tape's
alphabet and leaves input and output aside (Sections 2–3, pp. 534–535; see
`Turing.MultiTapeTM.hennieStearns`). -/
theorem hennieStearns_spec {t : ℕ} (hhalt : (tm.runFrom (tm.initCfg x) t).Halted) :
    ∃ T ≤ (80 * k + 2) * (t + 1) * (Nat.log 2 (t + 1) + 1),
      ((hennieStearns tm).runFrom ((hennieStearns tm).initCfg (x.map Sum.inl)) T).Halted ∧
      ((hennieStearns tm).runFrom ((hennieStearns tm).initCfg (x.map Sum.inl)) T).output =
        (tm.runFrom (tm.initCfg x) t).output.map Sum.inl := by
  classical
  have hex : ∃ n, (tm.runFrom (tm.initCfg x) n).state = none := ⟨t, hhalt⟩
  set n₀ := Nat.find hex
  have hn₀ : (tm.runFrom (tm.initCfg x) n₀).state = none := Nat.find_spec hex
  have hle : n₀ ≤ t := Nat.find_min' hex hhalt
  have hpos : n₀ ≠ 0 := by
    intro h
    rw [h] at hn₀
    exact Option.some_ne_none _ hn₀
  obtain ⟨n, hn⟩ : ∃ n, n₀ = n + 1 := Nat.exists_eq_succ_of_ne_zero hpos
  have hrun : (tm.runFrom (tm.initCfg x) n).state ≠ none :=
    Nat.find_min hex (show n < n₀ by omega)
  rw [hn] at hn₀ hle
  obtain ⟨T, Z, J, hist, hR, hlen, -, hT⟩ := reach tm x n hrun
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hrun
  rw [runFrom_succ] at hn₀
  obtain ⟨hh, hout⟩ := step_halt tm hR hq hn₀
  rw [← runFrom_add] at hh hout
  refine ⟨T + 1, ?_, hh, ?_⟩
  · have hcost : ∀ i, (blankTrack (Symbol := Symbol)).cost 0 (hist i) ≤
        t * (Nat.log 2 (t + 1) + 1) := fun i => by
      refine (ZTrack.cost_le (hist i) blankTrack_valid blankTrack_balanced).trans ?_
      have h1 : (hist i).length ≤ t := (hlen i).trans (by omega)
      exact Nat.mul_le_mul h1 (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)
    have hsum : ∑ i, 80 * (blankTrack (Symbol := Symbol)).cost 0 (hist i) ≤
        k * (80 * (t * (Nat.log 2 (t + 1) + 1))) := by
      calc ∑ i, 80 * (blankTrack (Symbol := Symbol)).cost 0 (hist i)
          ≤ ∑ _i : Fin k, 80 * (t * (Nat.log 2 (t + 1) + 1)) :=
            Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hcost i)
        _ = k * (80 * (t * (Nat.log 2 (t + 1) + 1))) := by simp
    have hL : 1 ≤ Nat.log 2 (t + 1) + 1 := by omega
    have : (t + 2) ≤ 2 * (t + 1) * (Nat.log 2 (t + 1) + 1) := by
      have := Nat.mul_le_mul_left (2 * (t + 1)) hL
      omega
    have h3 : k * (80 * (t * (Nat.log 2 (t + 1) + 1))) ≤
        80 * k * (t + 1) * (Nat.log 2 (t + 1) + 1) := by
      have := Nat.mul_le_mul_right (Nat.log 2 (t + 1) + 1) (Nat.le_succ t)
      calc k * (80 * (t * (Nat.log 2 (t + 1) + 1)))
          = 80 * k * (t * (Nat.log 2 (t + 1) + 1)) := by ring
        _ ≤ 80 * k * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := Nat.mul_le_mul_left _ this
        _ = 80 * k * (t + 1) * (Nat.log 2 (t + 1) + 1) := by ring
    have h4 : (80 * k + 2) * (t + 1) * (Nat.log 2 (t + 1) + 1) =
        80 * k * (t + 1) * (Nat.log 2 (t + 1) + 1) +
          2 * (t + 1) * (Nat.log 2 (t + 1) + 1) := by ring
    omega
  · rw [hout, runFrom_eq_of_halt tm _ hle (by rw [runFrom_succ]; exact hn₀), runFrom_succ]

end Turing.MultiTapeTM
