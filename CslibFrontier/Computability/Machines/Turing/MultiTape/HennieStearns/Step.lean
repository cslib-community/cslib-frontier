/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Op
public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Track
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A step of the simulated machine

After reading and writing the centers of all tracks (`step_apply`), the Hennie–Stearns machine
moves the tracks whose heads move, one after the other (`runFrom_ops`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}
  (tm : MultiTapeTM k Symbol State)

/-! ### The moving tracks -/

lemma nextMoving_some {mv : Fin k → SignType} {i₀ : ℕ} {i : Fin k} (h : nextMoving mv i₀ = some i) :
    i₀ ≤ i.val ∧ mv i ≠ 0 ∧ ∀ j : Fin k, i₀ ≤ j.val → j.val < i.val → mv j = 0 := by
  simp only [nextMoving] at h
  obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.1 h
  have hi : i ∈ (List.finRange k).filter fun j => i₀ ≤ j.val ∧ mv j ≠ 0 := by
    rw [htl]; exact List.mem_cons_self
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
  refine ⟨hi.1, hi.2, fun j hj hji => ?_⟩
  by_contra hmj
  have hj' : j ∈ (List.finRange k).filter fun j => i₀ ≤ j.val ∧ mv j ≠ 0 := by
    simp [hj, hmj]
  have hp := (List.pairwise_lt_finRange k).filter (fun j => decide (i₀ ≤ j.val ∧ mv j ≠ 0))
  rw [htl] at hp hj'
  rcases List.mem_cons.1 hj' with rfl | hmem
  · omega
  · have := (List.pairwise_cons.1 hp).1 j hmem
    exact absurd (Fin.lt_def.1 this) (by omega)

lemma nextMoving_none {mv : Fin k → SignType} {i₀ : ℕ} (h : nextMoving mv i₀ = none) :
    ∀ j : Fin k, i₀ ≤ j.val → mv j = 0 := by
  intro j hj
  simp only [nextMoving, List.head?_eq_none_iff, List.filter_eq_nil_iff, List.mem_finRange,
    decide_eq_true_eq, forall_const, not_and, not_not] at h
  exact h j hj

/-- The state starting the moves of the moving tracks from track `i₀` on. -/
def startOp (q : State) (mv : Fin k → SignType) (i₀ : ℕ) : HState k State :=
  match nextMoving mv i₀ with
  | some i => .op q mv i .scan
  | none => .apply q

/-- The tracks after the moves of the moving tracks from track `i₀` on. -/
def movedFrom (mv : Fin k → SignType) (i₀ : ℕ) (Z : Fin k → ZTrack Symbol) (J : ℕ) (i : Fin k) :
    ZTrack Symbol :=
  if i₀ ≤ i.val ∧ mv i ≠ 0 then (Z i).move J (srcSide mv i) else Z i

/-- The bound on the time of the moves of the moving tracks from track `i₀` on. -/
def opsTime (mv : Fin k → SignType) (i₀ : ℕ) (Z : Fin k → ZTrack Symbol) (J : ℕ) : ℕ :=
  ∑ i : Fin k, if i₀ ≤ i.val ∧ mv i ≠ 0 then 80 * 2 ^ (Z i).trig J (srcSide mv i) else 0

/-- **The moves of the moving tracks.** -/
theorem runFrom_ops (q : State) (mv : Fin k → SignType) (p : Fin (input.length + 2))
    (out : List (HSym k Symbol)) (i₀ : ℕ) (Z : Fin k → ZTrack Symbol) (J : ℕ)
    (hV : ∀ i, (Z i).Valid J) :
    ∃ T J', T ≤ opsTime mv i₀ Z J ∧ J ≤ J' ∧ (∀ i, (movedFrom mv i₀ Z J i).Valid J') ∧
      (hennieStearns tm).runFrom (hcfg (some (startOp q mv i₀)) p (encA Z J none) (encB [] [])
        0 1 out) T =
      hcfg (some (.apply q)) p (encA (movedFrom mv i₀ Z J) J' none) (encB [] []) 0 1 out := by
  rcases hn : nextMoving mv i₀ with _ | i
  · have h0 := nextMoving_none hn
    have hZ : movedFrom mv i₀ Z J = Z := funext fun i => by
      simp only [movedFrom]
      split_ifs with h
      · exact absurd (h0 i h.1) h.2
      · rfl
    refine ⟨0, J, Nat.zero_le _, le_rfl, fun i => by rw [hZ]; exact hV i, ?_⟩
    rw [hZ]
    simp only [startOp, hn]
    rfl
  · obtain ⟨hi₀, hmi, hbelow⟩ := nextMoving_some hn
    set s := srcSide mv i
    set Z₁ := Function.update Z i ((Z i).move J s)
    set J₁ := opLevels (Z i) J s
    have hJ₁ : J ≤ J₁ := by simp only [J₁, opLevels]; split_ifs <;> omega
    have hV₁ : ∀ i', (Z₁ i').Valid J₁ := fun i' => by
      by_cases h : i' = i
      · subst h
        simp only [Z₁, Function.update_self, J₁, opLevels]
        split_ifs with hj
        · exact (hV i').move s
        · exact (hV i').move_of_lt (lt_of_le_of_ne (ZTrack.trig_le (hV i') s) hj)
      · simp only [Z₁, Function.update_of_ne h]
        exact (hV i').mono hJ₁
    obtain ⟨T, J', hT, hJ', hV', hrun⟩ := runFrom_ops q mv p out (i.val + 1) Z₁ J₁ hV₁
    have hZ : movedFrom mv (i.val + 1) Z₁ J₁ = movedFrom mv i₀ Z J := funext fun i' => by
      simp only [movedFrom, Z₁]
      by_cases h : i' = i
      · subst h
        simp [hi₀, hmi, s]
      · rw [Function.update_of_ne h, ZTrack.move_mono (hV i') hJ₁]
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
        · rw [ite_eq_right fun h' => absurd h'.1 (by omega),
            ite_eq_right fun h' => absurd (hbelow i' h'.1 hlt) h'.2]
        · simp [show i.val + 1 ≤ i'.val by omega, show i₀ ≤ i'.val by omega]
    refine ⟨opTime (Z i) J s + T, J', ?_, hJ₁.trans hJ', fun i' => by rw [← hZ]; exact hV' i', ?_⟩
    · have hsum : opsTime mv i₀ Z J = 80 * 2 ^ (Z i).trig J s + opsTime mv (i.val + 1) Z₁ J₁ := by
        simp only [opsTime]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        simp only [hi₀, hmi, ne_eq, not_false_eq_true, and_self, ↓reduceIte, s]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        simp only [show ¬ i.val + 1 ≤ i.val by omega, false_and, ↓reduceIte, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun i' hi' => ?_
        have h := Finset.ne_of_mem_erase hi'
        simp only [Z₁, Function.update_of_ne h, J₁, ZTrack.trig_mono (hV i') hJ₁]
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
        · rw [ite_eq_right (fun h' => absurd (hbelow i' h'.1 hlt) h'.2),
            ite_eq_right (fun h' => by omega)]
        · simp only [show i.val + 1 ≤ i'.val by omega, show i₀ ≤ i'.val by omega, true_and]
      rw [hsum]
      have := opTime_le (hV i) s
      omega
    · rw [runFrom_add]
      have hop := runFrom_op tm q mv i p out Z hV
      simp only [startOp, hn]
      rw [show hcfg (some (HState.op q mv i Phase.scan)) p (encA Z J none) (encB [] []) 0 1 out =
        C q mv i p out .scan (encA Z J none) (encB [] []) 0 1 from rfl, hop, ← hZ]
      exact hrun
termination_by k - i₀
decreasing_by omega

end Turing.MultiTapeTM.HennieStearns
