/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Halting and divergence of native while loops

A sequence of configurations describes the loop at the boundaries between rounds.
When the test holds, the body must halt at the next boundary. There is no common
clock or space bound. The loop halts exactly at the first failed test, with the
tapes, heads and output specified by that boundary. If every test succeeds, the
loop reaches an unhalted boundary arbitrarily late and therefore diverges.

## Main results

* `Turing.MultiTapeTM.whileCond_reaches_checkpoint`: a true prefix of tests yields
  the corresponding unhalted boundary at a time at least the prefix length.
* `Turing.MultiTapeTM.whileCond_halted_run_iff`: the exact halted configuration
  is determined by the first failed test.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {c : Option Symbol → (Fin k → Option Symbol) → Bool} {tm : MultiTapeTM k Symbol State}

/-- A prefix of successful tests reaches its next boundary, taking at least one test step per
round. Only termination of the body in those rounds is assumed. -/
theorem whileCond_reaches_checkpoint (cfg : ℕ → Cfg k Symbol Unit input) (n : ℕ)
    (hround : ∀ i < n, c (cfg i).inputSymbol (cfg i).workTapeSymbols = true ∧
      ∃ t, tm.runFrom ((cfg i).withState (some tm.q₀)) t = (cfg (i + 1)).withState none) :
    ∃ t ≥ n, (whileCond c tm).runFrom ((cfg 0).withState (some (.inr ()))) t =
      (cfg n).withState (some (.inr ())) := by
  classical
  choose t ht using fun (i : ℕ) (hi : i < n) => (hround i hi).2
  let clock (i : ℕ) := if h : i < n then t i h else 0
  let space (i : ℕ) :=
    (MultiTapeNTM.RunPath.ofDeterministic tm ((cfg i).withState (some tm.q₀)) (clock i)).space
  obtain ⟨τ, hlow, _, hrun, _⟩ := RunsBetweenWhileCond.reaches_checkpoint cfg n clock space
    (fun i hi => ⟨(hround i hi).1, ⟨by simpa [clock, hi] using ht i hi, le_rfl⟩⟩)
  exact ⟨τ, hlow, hrun⟩

/-- With a correct body run for every successful test, halting occurs exactly at the first failed
test. The equivalence includes the entire halted configuration. -/
theorem whileCond_halted_run_iff (cfg : ℕ → Cfg k Symbol Unit input)
    (hbody : ∀ i, c (cfg i).inputSymbol (cfg i).workTapeSymbols = true →
      ∃ t, tm.runFrom ((cfg i).withState (some tm.q₀)) t = (cfg (i + 1)).withState none)
    (final : Cfg k Symbol (State ⊕ Unit) input) :
    (final.Halted ∧ ∃ t,
      (whileCond c tm).runFrom ((cfg 0).withState (some (.inr ()))) t = final) ↔
    ∃ n, (∀ i < n, c (cfg i).inputSymbol (cfg i).workTapeSymbols = true) ∧
      c (cfg n).inputSymbol (cfg n).workTapeSymbols = false ∧ final = (cfg n).withState none := by
  classical
  let test (i : ℕ) := c (cfg i).inputSymbol (cfg i).workTapeSymbols
  let start := (cfg 0).withState (some (.inr ()) : Option (State ⊕ Unit))
  have stop (n : ℕ) (hpre : ∀ i < n, test i = true) (hn : test n = false) :
      ∃ t, (whileCond c tm).runFrom start t = (cfg n).withState none := by
    obtain ⟨t, _, ht⟩ := whileCond_reaches_checkpoint (c := c) (tm := tm) cfg n
      (fun i hi => ⟨hpre i hi, hbody i (hpre i hi)⟩)
    refine ⟨t + 1, ?_⟩
    change c (cfg n).inputSymbol (cfg n).workTapeSymbols = false at hn
    rw [runFrom_succ, ht, RunsBetweenWhileCond.step_check, hn]
    rfl
  constructor
  · rintro ⟨hf, t, hrun⟩
    change (whileCond c tm).runFrom start t = final at hrun
    have he : ∃ n, test n = false := by
      by_contra! hall
      have hpre (i : ℕ) : test i = true := Bool.eq_true_of_not_eq_false (hall i)
      obtain ⟨u, hu, hcheck⟩ := whileCond_reaches_checkpoint (c := c) (tm := tm) cfg t
        (fun i _ => ⟨hpre i, hbody i (hpre i)⟩)
      have hhalt : ((whileCond c tm).runFrom start t).Halted := hrun ▸ hf
      change (whileCond c tm).runFrom start u = _ at hcheck
      rw [runFrom_eq_of_halt _ _ hu hhalt, hrun] at hcheck
      exact (show ¬((cfg t).withState (some (.inr ()) : Option (State ⊕ Unit))).Halted
        from by simp [Cfg.Halted, Cfg.withState]) (hcheck ▸ hf)
    let n := Nat.find he
    have hn : test n = false := Nat.find_spec he
    have hpre (i : ℕ) (hi : i < n) : test i = true :=
      Bool.eq_true_of_not_eq_false (Nat.find_min he hi)
    obtain ⟨u, hu⟩ := stop n hpre hn
    have heq : final = (cfg n).withState (none : Option (State ⊕ Unit)) := by
      rcases le_total t u with htu | hut
      · rw [runFrom_eq_of_halt _ _ htu (hrun ▸ hf), hrun] at hu
        exact hu
      · rw [runFrom_eq_of_halt _ _ hut (by rw [hu]; rfl), hu] at hrun
        exact hrun.symm
    exact ⟨n, hpre, hn, heq⟩
  · rintro ⟨n, hpre, hn, rfl⟩
    exact ⟨rfl, stop n hpre hn⟩

end Turing.MultiTapeTM
