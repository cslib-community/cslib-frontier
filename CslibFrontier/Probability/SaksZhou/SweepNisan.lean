/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SaksZhou.Nisan
public import CslibFrontier.Probability.SaksZhou.Sweep
public import CslibFrontier.Init
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Integer Nisan powering by a fixed sweep

For a matrix of integer transition counts with an absorbing sink, the seven-register sweep
can evaluate an entry of Nisan powering. The sweep accepts a numbered-letter function, which
on a valid seed and position must give the corresponding Nisan block.

## Main results

* `sweepHits_eq_nisanHits` identifies the sweep's counter with the number of Nisan starting blocks
  taking a given source to a given destination.
-/

public section

namespace Cslib.Probability.SaksZhou

open Finset Cslib.BitString Cslib.Crypto.PRG

private theorem scanWeightedRow_eq_walkStepOfCounts {n b : ℕ} (counts : ℕ → ℕ → ℕ)
    (i : Fin n) (x : BitString b) (hrow : ∑ j : Fin n, counts i j ≤ 2 ^ b) :
    scanWeightedRow n (counts i) (BitString.equivFin b x) =
      (walkStepOfCounts (Equiv.refl _) (BitString.equivFin b)
        (fun i j : Fin n => counts i j) (some i) x).elim n Fin.val := by
  have hfit : ∑ j : Fin n, counts i j ≤ Fintype.card (BitString b) := by
    simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hrow
  let dest := walkStepOfCounts (Equiv.refl _) (BitString.equivFin b)
    (fun i j : Fin n => counts i j) (some i) x
  have hd (j : Fin n) : scanWeightedRow n (counts i) (BitString.equivFin b x) = j ↔
      dest = some j := by
    rw [scanWeightedRow_eq_iff j.isLt]
    simpa only [Equiv.refl_apply, Fin.val_castLE, Fin.sum_univ_eq_sum_range (counts i)] using
      (walkStepOfCounts_eq_some_iff (Equiv.refl _) (BitString.equivFin b)
        (fun i j : Fin n => counts i j) i j x hfit).symm
  change _ = dest.elim n Fin.val
  cases h : dest with
  | some j => exact (hd j).2 h
  | none =>
    have hle := (scanWeightedRow_spec n (counts i) (BitString.equivFin b x)).1
    apply hle.antisymm
    by_contra! hc
    let j : Fin n := ⟨_, hc⟩
    have he := (hd j).1 rfl
    rw [h] at he
    contradiction


/-- Counting starting letters by sweeping all columns and positions gives the exact numerator
of a Nisan-powered entry. The natural identifier `n` is the absorbing sink. -/
theorem sweepHits_eq_nisanHits {n b k : ℕ} (scale : ℕ) (counts : ℕ → ℕ → ℕ)
    (hs : Fin k → ToeplitzSeed b) (label : ℕ → ℕ → ℕ)
    (hlabel : ∀ (x : BitString b) (t : Fin (2 ^ k)), label (BitString.equivFin b x) t =
      ↑(BitString.equivFin b (Nisan.blocks Cslib.Probability.toeplitzHash k x hs t)))
    (hrow : ∀ i : Fin n, ∑ j : Fin n, counts i j * scale ≤ 2 ^ b)
    (hsink : ∀ j, counts n j = 0) (src dst : Fin n) :
    (((fun s : SweepState => sweepUpdate n (2 ^ k) scale src dst label s (counts s.current s.j))^[
        2 ^ b * ((n + 2) * 2 ^ k + 1)]) (sweepStart n src)).hits =
      #{x : BitString b | (List.ofFn (Nisan.blocks Cslib.Probability.toeplitzHash k x hs)).foldl
        (walkStepOfCounts (Equiv.refl _) (BitString.equivFin b)
          (fun i j : Fin n => counts i j * scale)) (some src) = some dst} := by
  let w (i j : ℕ) := counts i j * scale
  let code (s : Option (Fin n)) := s.elim n Fin.val
  let step := walkStepOfCounts (Equiv.refl _) (BitString.equivFin b) (fun i j : Fin n => w i j)
  have hstep (s : Option (Fin n)) (x : BitString b) :
      scanWeightedRow n (w (code s)) (BitString.equivFin b x) = code (step s x) := by
    cases s with
    | some i => exact scanWeightedRow_eq_walkStepOfCounts w i x (hrow i)
    | none =>
      have hz : step none x = none :=
        walkStepOfCounts_none (Equiv.refl _) (BitString.equivFin b) _ x
      rw [hz]
      simp only [code, Option.elim_none]
      have spec := scanWeightedRow_spec n (w n) (BitString.equivFin b x)
      have hle := spec.1
      apply hle.antisymm
      by_contra! h
      have := spec.2.2 h
      simp [w, hsink] at this
  have traj (x : BitString b) :
      (List.range (2 ^ k)).foldl (fun u t => scanWeightedRow n (w u)
          (label (BitString.equivFin b x) t)) src =
        code ((List.ofFn (Nisan.blocks Cslib.Probability.toeplitzHash k x hs)).foldl step
          (some src)) := by
    rw [← List.map_coe_finRange_eq_range, List.foldl_map, List.ofFn_eq_map, List.foldl_map]
    refine List.foldl_hom code (init := some src)
      (g₁ := fun s t => step s (Nisan.blocks Cslib.Probability.toeplitzHash k x hs t))
      (g₂ := fun u (t : Fin (2 ^ k)) => scanWeightedRow n (w u)
        (label (BitString.equivFin b x) t)) fun s t => ?_
    rw [hlabel x t]
    exact hstep _ _
  have hcode (s : Option (Fin n)) : code s = dst ↔ s = some dst := by
    cases s with
    | none => simp [code, Nat.ne_of_gt dst.isLt]
    | some j => simp [code, Fin.ext_iff]
  rw [iterate_sweepUpdate_hits, List.countP_range_eq_card_filter, Finset.card_filter,
    ← (BitString.equivFin b).sum_comp, Finset.card_filter]
  refine sum_congr rfl fun x _ => ?_
  simp only [decide_eq_true_eq]
  change (if (List.range (2 ^ k)).foldl (fun u t => scanWeightedRow n (w u)
      (label (BitString.equivFin b x) t)) src = dst then 1 else 0) = _
  rw [traj x]
  simp only [hcode]
  rfl

end Cslib.Probability.SaksZhou
