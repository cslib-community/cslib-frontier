/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.CrossingSequence
import CslibFrontier.Computability.Machines.Turing.SingleTape.PostTuringMachine
import Mathlib.Tactic.Ring

/-!
# Absolute runs that produce outputs, and sweeps

Two tools for proving upper bounds on single-tape machines (`Cslib.Turing.SingleTapeTM`) in the
absolute coordinates of `AbsCfg`:

* `outputsWithinTime_of_absRun`: if the absolute run from `absInit l` has halted by step `t`
  with head at cell `0` and tape `BiTape.mk₁ l'`, then `tm.OutputsWithinTime l l' t`. So an upper
  bound may be proved entirely on integer-indexed tapes.
* `AbsCfg.run_sweep`: a *sweep* is a stretch of a run in which the machine walks in one direction
  over a block of cells, rewriting each one and updating finite data carried in its state, as
  described by a function `f : D → Option Γ → D × Option Γ`. The run over the block is computed
  by `sweepOut f`, which threads the data along the block. Only the cells of the block need to
  follow `f`, so a sweep may stop before a cell that the machine treats differently.

## Main definitions

* `Cslib.Turing.SingleTapeTM.sweepOut`: the data and rewritten cells after a sweep over a list.

## Main results

* `Cslib.Turing.BiTape.read_injective`: a tape is determined by what it reads.
* `Cslib.Turing.SingleTapeTM.outputsWithinTime_of_absRun`.
* `Cslib.Turing.SingleTapeTM.AbsCfg.run_sweep`.
-/

public section

open Cslib Cslib.Turing Relation

namespace Cslib.Turing

/-- A Mathlib tape is determined by its cells. -/
private theorem tape_ext {Γ : Type*} [Inhabited Γ] {T₁ T₂ : _root_.Turing.Tape Γ}
    (h : ∀ i, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  obtain ⟨a, L, R⟩ := T₁
  obtain ⟨b, L', R'⟩ := T₂
  congr 1
  · exact h 0
  · exact _root_.Turing.ListBlank.ext fun n => h (Int.negSucc n)
  · exact _root_.Turing.ListBlank.ext fun n => h ((n + 1 : ℕ) : ℤ)

/-- A tape is determined by its contents relative to the head. -/
theorem BiTape.read_injective {Symbol : Type*} :
    Function.Injective (BiTape.read (Symbol := Symbol)) :=
  fun t₁ t₂ h => BiTape.equivTape.injective (tape_ext fun i => by
    simp only [BiTape.nth_equivTape, h])

namespace SingleTapeTM

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] {tm : SingleTapeTM Γ}

private theorem exists_relatesInSteps_of_agrees :
    ∀ (t : ℕ) (c : tm.Cfg) (a : tm.AbsCfg), Agrees c a → (a.run t).state = none →
      ∃ m ≤ t, ∃ c', RelatesInSteps tm.TransitionRelation c c' m ∧ Agrees c' (a.run t)
  | 0, c, a, h, _ => ⟨0, le_rfl, c, .refl c, h⟩
  | t + 1, c, a, h, hhalt => by
    rcases hs : a.state with _ | q
    · rw [AbsCfg.run_of_none hs] at hhalt ⊢
      exact ⟨0, Nat.zero_le _, c, .refl c, h⟩
    · rcases c with ⟨_ | q', tape⟩
      · exact absurd ((show _ ∧ _ from h).1.trans hs) (by simp)
      · obtain ⟨m, hm, c', hrun, hag⟩ := exists_relatesInSteps_of_agrees t _ a.next
          (Agrees.step h (step_some tm q' tape)) (by rwa [AbsCfg.run_succ] at hhalt)
        rw [AbsCfg.run_succ]
        exact ⟨m + 1, by omega, c', .head _ _ _ _ (step_some tm q' tape) hrun, hag⟩

/-- An upper bound proved in absolute coordinates: if the absolute run on `l` has halted by step
`t` with the head at cell `0` and the tape holding `l'`, then `tm` outputs `l'` on `l` within `t`
steps. -/
theorem outputsWithinTime_of_absRun {l l' : List Γ} {t : ℕ}
    (h : (tm.absInit l).run t = ⟨none, 0, (BiTape.mk₁ l').read⟩) :
    tm.OutputsWithinTime l l' t := by
  obtain ⟨m, hm, c', hrun, hag⟩ :=
    exists_relatesInSteps_of_agrees t _ _ (agrees_init l) (by rw [h])
  obtain ⟨hstate, hrep⟩ := (show _ ∧ _ from hag)
  rw [h] at hstate hrep
  have htape : c'.BiTape = BiTape.mk₁ l' := BiTape.read_injective (funext fun i => by
    simpa using hrep i)
  obtain ⟨_ | q, tape⟩ := c'
  · simp only at htape
    subst htape
    exact ⟨m, hm, hrun⟩
  · simp at hstate

/-- The data and the rewritten cells after sweeping `f` along the cells `cs`, starting with the
data `d`. -/
@[expose] def sweepOut {D : Type*} (f : D → Option Γ → D × Option Γ) :
    D → List (Option Γ) → D × List (Option Γ)
  | d, [] => (d, [])
  | d, a :: as => ((sweepOut f (f d a).1 as).1, (f d a).2 :: (sweepOut f (f d a).1 as).2)

omit [Inhabited Γ] [Fintype Γ] in
@[simp] lemma length_sweepOut {D : Type*} (f : D → Option Γ → D × Option Γ) (d : D)
    (cs : List (Option Γ)) : (sweepOut f d cs).2.length = cs.length := by
  induction cs generalizing d with
  | nil => rfl
  | cons a as ih => simp [sweepOut, ih]

/-- **Sweeps.** Suppose that in the states `S d` the machine rewrites each cell `a` of the block
`cs` (blank or not) to `(f d a).2`, moves in direction `dir` and continues in `S (f d a).1`.
Started in `S d` on the block `cs`, read in the direction of travel, it runs over the whole
block in `cs.length` steps, rewriting it to `(sweepOut f d cs).2`, leaving every other cell alone,
and ending in `S (sweepOut f d cs).1` just past the block. -/
theorem AbsCfg.run_sweep {D : Type*} (S : D → tm.State) (f : D → Option Γ → D × Option Γ)
    (dir : _root_.Turing.Dir) :
    ∀ (cs : List (Option Γ)),
      (∀ d, ∀ a ∈ cs, tm.tr (S d) a = (⟨(f d a).2, some dir⟩, some (S (f d a).1))) →
      ∀ (d : D) (c : tm.AbsCfg), c.state = some (S d) →
      (∀ j (hj : j < cs.length), c.cells (c.pos + moveShift (some dir) * j) = cs[j]) →
      (c.run cs.length).state = some (S (sweepOut f d cs).1) ∧
      (c.run cs.length).pos = c.pos + moveShift (some dir) * cs.length ∧
      (∀ j (hj : j < cs.length), (c.run cs.length).cells (c.pos + moveShift (some dir) * j) =
        (sweepOut f d cs).2[j]'(by simpa using hj)) ∧
      (∀ z, (∀ j < cs.length, z ≠ c.pos + moveShift (some dir) * j) →
        (c.run cs.length).cells z = c.cells z)
  | [], _, d, c, hstate, _ => ⟨hstate, by simp [AbsCfg.run_zero], fun _ hj => absurd hj (by simp),
      fun _ _ => rfl⟩
  | a :: as, hS, d, c, hstate, hcells => by
    have hσ : moveShift (some dir) = 1 ∨ moveShift (some dir) = -1 := by
      cases dir <;> simp [moveShift]
    have hnext : c.next = ⟨some (S (f d a).1), c.pos + moveShift (some dir),
        Function.update c.cells c.pos (f d a).2⟩ := by
      have ha := hcells 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.cast_zero, mul_zero, add_zero] at ha
      rcases c with ⟨st, p, cells⟩
      simp only at hstate ha
      subst hstate
      simp only [AbsCfg.next, ha, hS d a (by simp)]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := AbsCfg.run_sweep S f dir as
      (fun d a ha => hS d a (List.mem_cons_of_mem _ ha)) (f d a).1 c.next
      (by rw [hnext]) (fun j hj => by
        rw [hnext]
        simp only
        rw [Function.update_of_ne (by rcases hσ with h | h <;> rw [h] <;> omega)]
        have := hcells (j + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at this
        rw [← this]
        congr 1
        push_cast
        ring)
    have hrun : c.run (a :: as).length = c.next.run as.length := AbsCfg.run_succ _ _
    rw [hrun]
    refine ⟨h₁, ?_, fun j hj => ?_, fun z hz => ?_⟩
    · rw [h₂, hnext]
      simp only [List.length_cons, Nat.cast_succ]
      ring
    · rcases j with _ | j
      · rw [h₄ _ fun i hi => ?_]
        · rw [hnext]
          simp [sweepOut]
        · rw [hnext]
          simp only
          rcases hσ with h | h <;> rw [h] <;> omega
      · have := h₃ j (by simpa using hj)
        rw [hnext] at this ⊢
        simp only at this ⊢
        rw [show c.pos + moveShift (some dir) * ((j + 1 : ℕ) : ℤ) =
          c.pos + moveShift (some dir) + moveShift (some dir) * (j : ℤ) by push_cast; ring, this]
        simp [sweepOut]
    · rw [h₄ z fun j hj => ?_]
      · rw [hnext]
        simp only
        rw [Function.update_of_ne (by simpa using hz 0 (by simp))]
      · rw [hnext]
        simp only
        have := hz (j + 1) (by simp; omega)
        intro heq
        apply this
        rw [heq]
        push_cast
        ring

end SingleTapeTM

end Cslib.Turing
