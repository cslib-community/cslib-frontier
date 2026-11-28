/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
public import CslibFrontier.Foundations.Data.Nat.IterLog
import CslibFrontier.Tactic.Realize

/-!
# Pure-register Word-RAM logarithm and iterated logarithm routines

This module provides zero-memory-cost (`memoryCost = 0`) Word-RAM programs computing `Nat.log 2 x`
and `Nat.iterLog k x` via pure register arithmetic (`boundedWhile` and `iterate`), certified with
both `Memory.FramedTriple` (`cost = 0`, `S = ∅`) and `Realizes .exact`.

## Main definitions

* `natLog2Prog`: compute `⌊log₂ x⌋` using register right-shifts with zero memory accesses.
* `iterLogProg`: compute the `k`-fold iterated floor logarithm `Nat.iterLog k x` with zero memory
  accesses.

## Main results

* `natLog2Prog_spec`, `realizes_natLog2Prog`: `Memory.FramedTriple` (`cost = 0`) and
  `Realizes .exact` (`work = Nat.log 2 x + 2`) certificates for `natLog2Prog`.
* `iterLogProg_spec`, `realizes_iterLogProg`: `Memory.FramedTriple` (`cost = 0`) and
  `Realizes .exact` (`work = k * (Nat.log 2 x + 3)`) certificates for `iterLogProg`.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

private def natLog2Step (q : Unit × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  pure (q.2.1 >>> 1, q.2.2 + 1)

/-- Compute `⌊log₂ x⌋` using register shifts with zero memory accesses (`memoryCost = 0`). -/
def natLog2Prog (x : ℕ) : Memory.Prog ℕ := do
  let p ← boundedWhile (fun _ (p : ℕ × ℕ) => 1 < p.1) natLog2Step () (Nat.log 2 x) (x, 0)
  pure p.2

private theorem natLog2_loop_spec (w fuel a b : ℕ) (hfuel : Nat.log 2 a ≤ fuel)
    (s : Memory.State) :
    let prog := boundedWhile (fun _ (p : ℕ × ℕ) => 1 < p.1)
      (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1)) () fuel (a, b)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ((Memory.spec 0).clientResult s prog).2 = b + Nat.log 2 a ∧
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s = 0 := by
  induction fuel generalizing a b with
  | zero =>
    have ha : ¬(1 < a) := by
      intro hlt
      have hpos : 0 < Nat.log 2 a := Nat.log_pos (by decide) hlt
      omega
    have hlog : Nat.log 2 a = 0 := Nat.log_eq_zero_iff.mpr (Or.inl (by omega))
    simp only [boundedWhile, StateTransitionSpec.clientResult_pure, memoryCost_pure, hlog,
      Nat.add_zero]
    exact ⟨trivial, trivial, rfl, trivial⟩
  | succ fuel ih =>
    by_cases ha : 1 < a
    · have hdiv : a >>> 1 = a / 2 := by rw [Nat.shiftRight_eq_div_pow]
      have hlog : Nat.log 2 a = Nat.log 2 (a / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by decide) ha
      have hrec := ih (a / 2) (b + 1) (by omega)
      have hprog : boundedWhile (fun _ (p : ℕ × ℕ) => 1 < p.1)
          (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1)) () (fuel + 1) (a, b) =
          boundedWhile (fun _ (p : ℕ × ℕ) => 1 < p.1)
            (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1)) () fuel
            (a / 2, b + 1) := by
        simp only [boundedWhile, ha, ↓reduceIte, pure_bind, hdiv]
      rw [hprog]
      refine ⟨hrec.1, ?_, hrec.2.2.1, hrec.2.2.2⟩
      rw [hrec.2.1, hlog]
      omega
    · have hlog : Nat.log 2 a = 0 := Nat.log_eq_zero_iff.mpr (Or.inl (by omega))
      simp only [boundedWhile, ha, ↓reduceIte, StateTransitionSpec.clientResult_pure,
        memoryCost_pure, hlog, Nat.add_zero]
      exact ⟨trivial, trivial, rfl, trivial⟩

/-- Framed specification for `natLog2Prog`: returns `Nat.log 2 x` in `memoryCost = 0` and leaves
memory unchanged (`s' = s`). -/
theorem natLog2Prog_spec (w x : ℕ) (s : Memory.State) :
    Memory.FramedTriple w s (natLog2Prog x) 0 ∅ fun res s' =>
      s' = s ∧ res = Nat.log 2 x := by
  have h := natLog2_loop_spec w (Nat.log 2 x) x 0 le_rfl s
  rw [framedTriple_iff_realization]
  have hprog : natLog2Prog x = (boundedWhile (fun _ (p : ℕ × ℕ) => 1 < p.1)
      (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1)) () (Nat.log 2 x) (x, 0) >>=
      fun p => pure p.2) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hprog, validHistory_bind']; exact ⟨h.1, trivial⟩
  · rw [hprog, memoryCost_bind', memoryCost_pure, h.2.2.2]
  · rw [hprog, StateTransitionSpec.clientState_bind, h.2.2.1]
    exact Memory.Modifies.refl ∅ s
  · rw [hprog, StateTransitionSpec.clientState_bind, h.2.2.1]; rfl
  · rw [hprog, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    simpa using h.2.1

/-- Uniform `Realizes .exact` certificate for `natLog2Prog` with zero memory accesses and
`O(Nat.log 2 x + 1)` local register work. -/
theorem realizes_natLog2Prog :
    Realizes .exact natLog2Prog WordEncoding.encode WordEncoding.encode
      (fun w _ _ => Fits w 1) (fun x _ => Nat.log 2 x + 2) := by
  have hraw : Realizes .exact natLog2Prog WordEncoding.encode WordEncoding.encode
      (fun w x s =>
        Fits w 1 ∧
        whileSafe (fun _ (p : ℕ × ℕ) => 1 < p.1)
          (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1))
          (fun w (q : Unit × (ℕ × ℕ)) _ => Fits w (q.2.2 + 1)) w () (Nat.log 2 x) (x, 0) s)
      (fun x s =>
        whileWork (fun _ (p : ℕ × ℕ) => 1 < p.1)
          (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1))
          (fun _ _ => 0) () (Nat.log 2 x) (x, 0) s + 1) := by
    unfold natLog2Prog natLog2Step
    realize
    · exact h.1
    · exact fun _ => whileSafe_imp _ _ (fun _ => Iff.rfl) (fun _ => rfl)
        (fun p _ _ hp => ⟨h.1, hp⟩) h.2
    · exact Nat.le_succ _
  refine hraw.consequence_work (fun w x s hwords _ hv h1 => ?_)
    (fun _ x s _ _ _ _ => ?_)
  · refine ⟨h1, ?_⟩
    refine whileSafe_of_measure (fun _ (p : ℕ × ℕ) => 1 < p.1)
      (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1))
      (fun w (q : Unit × (ℕ × ℕ)) _ => Fits w (q.2.2 + 1)) w ()
      (fun p _ => p.2 + Nat.log 2 p.1 ≤ Nat.log 2 x)
      (fun p _ => Nat.log 2 p.1)
      (fun p _ _ hr hg => by
        have hpos : 0 < Nat.log 2 p.1 := Nat.log_pos (by decide) hg
        omega)
      (fun p t hI hg _ => ?_)
      (by simp) le_rfl ((validHistory_bind' w _ _ s).mp hv).1
    have hdiv : p.1 >>> 1 = p.1 / 2 := by rw [Nat.shiftRight_eq_div_pow]
    have hlog : Nat.log 2 p.1 = Nat.log 2 (p.1 / 2) + 1 :=
      Nat.log_of_one_lt_of_le (by decide) hg
    have hx : Fits w x := hwords 0
    have hlogx : Nat.log 2 x ≤ x := Nat.log_le_self 2 x
    dsimp only
    refine ⟨hx.of_le (by omega), ?_, ?_⟩
    · change (p.2 + 1) + Nat.log 2 (p.1 >>> 1) ≤ Nat.log 2 x
      rw [hdiv]
      omega
    · change Nat.log 2 (p.1 >>> 1) < Nat.log 2 p.1
      rw [hdiv]
      omega
  · have hle := whileWork_le (fun _ (p : ℕ × ℕ) => 1 < p.1)
      (fun (q : Unit × (ℕ × ℕ)) => pure (q.2.1 >>> 1, q.2.2 + 1))
      (work := fun _ _ => 0) (K := 0) (fun _ _ => le_rfl) () (Nat.log 2 x) (x, 0) s
    omega

/-- Compute the iterated base-2 floor logarithm `Nat.iterLog k x` with zero memory accesses
(`memoryCost = 0`). -/
def iterLogProg (k x : ℕ) : Memory.Prog ℕ :=
  iterate (fun (q : Unit × ℕ) => natLog2Prog q.2) () k x

/-- Framed specification for `iterLogProg`: returns `Nat.iterLog k x` in `memoryCost = 0` and
leaves memory unchanged (`s' = s`). -/
theorem iterLogProg_spec (w k x : ℕ) (s : Memory.State) :
    Memory.FramedTriple w s (iterLogProg k x) 0 ∅ fun res s' =>
      s' = s ∧ res = Nat.iterLog k x := by
  induction k generalizing x with
  | zero => exact Memory.FramedTriple.pure ⟨rfl, rfl⟩
  | succ k ih =>
    have hstep : Memory.FramedTriple w s (natLog2Prog x) 0 ∅ fun a s₁ =>
        Memory.FramedTriple w s₁ (iterLogProg k a) 0 ∅ fun res s' =>
          s' = s ∧ res = Nat.iterLog (k + 1) x := by
      refine (natLog2Prog_spec w x s).mono le_rfl fun a s₁ ⟨hs₁, ha⟩ => ?_
      subst hs₁ ha
      exact (ih (Nat.log 2 x)).mono le_rfl fun res s' ⟨hs', hres⟩ =>
        ⟨hs', hres.trans (Nat.iterLog_succ_apply k x).symm⟩
    have hprog : iterLogProg (k + 1) x = (natLog2Prog x >>= fun a => iterLogProg k a) := rfl
    rw [hprog]
    exact Memory.FramedTriple.bind_same hstep

private theorem iterLog_work_le (x k a : ℕ) (ha : a ≤ x) (s : Memory.State) :
    iterationWork (fun (q : Unit × ℕ) => natLog2Prog q.2)
      (fun q _ => Nat.log 2 q.2 + 2) () k a s ≤ k * (Nat.log 2 x + 3) := by
  induction k generalizing a s with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have ha_log : Nat.log 2 a ≤ Nat.log 2 x := Nat.log_mono_right ha
    have hstep := natLog2Prog_spec 0 a s
    obtain ⟨_, _, _, hst, hres⟩ := Memory.framedTriple_iff.mp hstep
    simp only [iterationWork]
    have hnext : (Memory.spec 0).clientResult s (natLog2Prog a) ≤ x := by
      rw [hres]
      exact (Nat.log_le_self 2 a).trans ha
    have ih' := ih _ hnext ((Memory.spec 0).clientState s (natLog2Prog a))
    rw [Nat.succ_mul]
    omega

/-- Uniform `Realizes .exact` certificate for `iterLogProg` with zero memory accesses and
`O(k * (Nat.log 2 x + 3))` local register work. -/
theorem realizes_iterLogProg :
    Realizes .exact (fun (k, x) => iterLogProg k x) WordEncoding.encode WordEncoding.encode
      (fun w _ _ => Fits w 1) (fun (k, x) _ => k * (Nat.log 2 x + 3)) := by
  have hraw : Realizes .exact (fun d : ℕ × ℕ => iterLogProg d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s =>
        iterationSafe (fun q : (ℕ × ℕ) × ℕ => natLog2Prog q.2)
          (fun w _ _ => Fits w 1) w d d.1 d.2 s)
      (fun d s =>
        iterationWork (fun (q : Unit × ℕ) => natLog2Prog q.2)
          (fun q _ => Nat.log 2 q.2 + 2) () d.1 d.2 s) := by
    unfold iterLogProg
    realize [realizes_natLog2Prog]
    exact iterationSafe_imp h (fun _ => rfl) (fun _ _ hs => hs)
  refine (hraw.congr (fun ⟨_, _⟩ => rfl)).consequence_work
    (fun w d s _ _ _ h1 => ?_) (fun _ d s _ _ _ _ => ?_)
  · rcases d with ⟨k, x⟩
    have hsafe : ∀ n a t,
        iterationSafe (fun q : (ℕ × ℕ) × ℕ => natLog2Prog q.2)
          (fun w _ _ => Fits w 1) w (k, x) n a t := by
      intro n
      induction n with
      | zero => intro _ _; trivial
      | succ n ih => intro _ _; exact ⟨h1, ih _ _⟩
    exact hsafe k x s
  · rcases d with ⟨k, x⟩
    exact iterLog_work_le x k x le_rfl s

end Cslib.WordRAM.Realization
