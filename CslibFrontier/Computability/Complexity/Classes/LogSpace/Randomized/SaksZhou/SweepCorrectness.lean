/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Entry
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.SweepSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.SaksZhouSeed
public import CslibFrontier.Probability.SaksZhou.SweepNisan
public import CslibFrontier.Init

/-!
# Recursive packed Saks–Zhou sweeps

The nested sweep reads generator blocks and rounding shifts from one shared binary seed. At every
depth its output is the exact integer numerator of the rounded Nisan iteration for valid entries;
queries outside the matrix have value zero.

## Main definitions

* `nisanSweepLoop` specializes the nested loop to packed Nisan blocks and integer snapping.
* `saksZhouEntryLoop` supplies the parameters and half-coin base matrix of the BPL estimator.

## Main results

* `nisanSweepLoop_run` recovers each dyadic Nisan iterate at every depth.
* `saksZhouEntryLoop_run` identifies the bounded root job with the compact estimator's packed entry.
* `saksZhouEntryLoop_run_le` bounds every recursive answer by the fixed-point denominator.
-/

public section

namespace Cslib.Probability.SaksZhou

open Turing.MultiTapeTM Cslib.BitString

/-- A nested sweep for dyadic matrices. The common seed supplies the Nisan blocks and every
rounding shift. The base callback returns integer numerators at denominator `2 ^ d`. -/
abbrev nisanSweepLoop {α : Type} (width b d k seed : α → ℕ) (base : α → SweepJob → ℕ) :
    NestedLoop α SweepJob SweepState ℕ :=
  sweepLoop width (fun a => 2 ^ k a) (fun a => 2 ^ b a) (fun a => 2 ^ (b a - d a))
    (fun a => nisanBlockValue (b a) (k a) (seed a)) base (fun a level hits =>
      snapCount (2 ^ d a) hits (2 ^ b a)
        (nisanRoundingShift (b a) (k a) (d a) (seed a) (level - 1)))

/-- The full native sweep recovers the seeded numerator at each depth, and returns zero outside
the matrix. Each level uses the same hash fields and its initial segment of shifts. -/
theorem nisanSweepLoop_run {α : Type} (width b d k seed : α → ℕ) (base : α → SweepJob → ℕ)
    (a : α) (hdb : d a ≤ b a) (hrow : ∀ i : Fin (width a),
      ∑ j : Fin (width a), base a ⟨i, j⟩ ≤ 2 ^ d a) (level : ℕ) (q : SweepJob) :
    (nisanSweepLoop width b d k seed base).run a level q =
      let z := nisanShiftSeedOfNat (b a) (k a) level (d a) (seed a)
      if hi : q.row < width a then
        if hj : q.column < width a then
          nisanSnapCounts (Equiv.refl _) (b a) (d a) (k a) z.1
            (fun i j : Fin (width a) => base a ⟨i, j⟩) level z.2 ⟨_, hi⟩ ⟨_, hj⟩
        else 0
      else 0 := by
  let L := nisanSweepLoop width b d k seed base
  let M : Matrix (Fin (width a)) (Fin (width a)) ℕ := fun i j => base a ⟨i, j⟩
  let sol l := nisanShiftSeedOfNat (b a) (k a) l (d a) (seed a)
  let count l := nisanSnapCounts (Equiv.refl _) (b a) (d a) (k a) (sol l).1 M l (sol l).2
  change L.run a level q = if hi : q.row < _ then
    (if hj : q.column < _ then count level ⟨_, hi⟩ ⟨_, hj⟩ else 0) else 0
  induction level generalizing q with
  | zero =>
    rw [NestedLoop.run]
    change (if q.row < width a ∧ q.column < width a then base a q else 0) = _
    split_ifs <;> simp_all [count, nisanSnapCounts, M]
  | succ r ih =>
    let raw (i j : ℕ) := L.run a r ⟨i, j⟩
    have hraw (i j : Fin (width a)) : raw i j = count r i j := by
      simpa only [raw, i.isLt, j.isLt, ↓reduceDIte] using ih ⟨i, j⟩
    have hsink (j : ℕ) : raw (width a) j = 0 := by
      simpa only [raw, lt_self_iff_false, ↓reduceDIte] using ih ⟨width a, j⟩
    have hscaled (i : Fin (width a)) :
        ∑ j : Fin (width a), raw i j * 2 ^ (b a - d a) ≤ 2 ^ b a := by
      have hsum : ∑ j, count r i j ≤ 2 ^ d a := by
        cases r with
        | zero => exact hrow i
        | succ l => exact sum_nisanSnapCounts_le _ _ _ _ _ _ _ _ _
      simp_rw [hraw]
      rw [← Finset.sum_mul, ← Nat.sub_add_cancel hdb, pow_add]
      simpa only [Nat.add_sub_cancel, Nat.mul_comm] using
        Nat.mul_le_mul_right (2 ^ (b a - d a)) hsum
    have hletter (x : BitString (b a)) (t : Fin (2 ^ k a)) :
        nisanBlockValue (b a) (k a) (seed a) (BitString.equivFin (b a) x) t = ↑(BitString.equivFin
          (b a) (Crypto.PRG.Nisan.blocks Cslib.Probability.toeplitzHash (k a) x (sol r).1 t)) := by
      simpa only [BitString.testBit_equivFin, sol] using
        nisanBlockValue_eq (b a) (k a) r (d a) (seed a) (BitString.equivFin _ x).isLt t.isLt
    rw [NestedLoop.run]
    change (if q.row < width a ∧ q.column < width a then _ else 0) = _
    split_ifs with h hi hj
    · have he := sweepHits_eq_nisanHits (2 ^ (b a - d a)) raw (sol r).1 _ hletter hscaled hsink
        (⟨_, hi⟩ : Fin (width a)) (⟨_, hj⟩ : Fin (width a))
      change snapCount (2 ^ d a) _ (2 ^ b a) _ = _
      dsimp only [count, nisanSnapCounts, Matrix.of_apply]
      simp_rw [hraw] at he
      exact congrArg (fun hits => snapCount (2 ^ d a) hits (2 ^ b a)
        (nisanRoundingShift (b a) (k a) (d a) (seed a) r)) he
    all_goals simp_all

/-- Every answer, including a dummy query outside the matrix, fits the fixed-point precision. -/
theorem nisanSweepLoop_run_le {α : Type} (width b d k seed : α → ℕ) (base : α → SweepJob → ℕ)
    (a : α) (hdb : d a ≤ b a) (hrow : ∀ i : Fin (width a),
      ∑ j : Fin (width a), base a ⟨i, j⟩ ≤ 2 ^ d a) (level : ℕ) (q : SweepJob) :
    (nisanSweepLoop width b d k seed base).run a level q ≤ 2 ^ d a := by
  rw [nisanSweepLoop_run _ _ _ _ _ _ a hdb hrow]
  dsimp only
  split_ifs with hi hj
  · cases level with
    | zero =>
      exact (Finset.single_le_sum (fun (j : Fin (width a)) _ => Nat.zero_le (base a ⟨q.row, j⟩))
        (Finset.mem_univ (⟨_, hj⟩ : Fin (width a)))).trans (hrow ⟨_, hi⟩)
    | succ r =>
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)).trans
        (sum_nisanSnapCounts_le _ _ _ _ _ _ _ _ _)
  all_goals exact Nat.zero_le _

end Cslib.Probability.SaksZhou

namespace Turing.MultiTapePTM.ConfigurationGraph

open Cslib.Probability.SaksZhou MultiTapeNTM.ConfigurationGraph MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State)

/-- The nested-loop program for a compact configuration matrix, with the seed and input word
shared across all recursive levels. -/
noncomputable abbrev saksZhouEntryLoop (c clk : ℕ) :
    NestedLoop (SaksZhouEntry × List Bool) SweepJob SweepState ℕ :=
  let radixOf (p : SaksZhouEntry × List Bool) := radix (radixExponent State c) p.2.length
  let precision (p : SaksZhouEntry × List Bool) := saksZhouPrecision clk p.2.length
  nisanSweepLoop (fun p => vertexBound (k := k) (radixOf p)) (fun p => 2 * (5 * precision p))
    precision (fun p => saksZhouLevels clk p.2.length) (fun p => p.1.seed) (fun p j =>
      coinCountWithSymbol M (radixOf p) p.2.length j.row j.column p.2[queryIndex (k := k)
        (radixOf p) j.row]? * 2 ^ (precision p - 1))

private theorem clamp_entry (n r c : ℕ) (f : Fin n → Fin n → ℕ) :
    (if hr : min r (n + 1) < n then
      if hc : min c (n + 1) < n then f ⟨_, hr⟩ ⟨_, hc⟩ else 0 else 0) =
    (if hr : r < n then if hc : c < n then f ⟨_, hr⟩ ⟨_, hc⟩ else 0 else 0) := by
  by_cases hr : r < n
  · simp only [min_eq_left (by omega : r ≤ n + 1), hr, ↓reduceDIte]
    by_cases hc : c < n
    · simp [min_eq_left (by omega : c ≤ n + 1), hc]
    · simp [hc, show ¬min c (n + 1) < n by omega]
  · simp [hr, show ¬min r (n + 1) < n by omega]

/-- The concrete program returns the final packed entry. Clamping the two identifiers to the
marker `N+1` bounds the initial job even when the input supplies arbitrarily large identifiers. -/
theorem saksZhouEntryLoop_run (c clk : ℕ) (p : SaksZhouEntry × List Bool) :
    let n := vertexBound (k := k) (radix (radixExponent State c) p.2.length)
    (saksZhouEntryLoop M c clk).run p (saksZhouLevels clk p.2.length)
      ⟨min p.1.row (n + 1), min p.1.column (n + 1)⟩ = saksZhouEntryValue M c clk p := by
  let d := saksZhouPrecision clk p.2.length
  let B := radix (radixExponent State c) p.2.length
  let n := vertexBound (k := k) B
  have hd : 0 < d := by simp only [d, saksZhouPrecision]; omega
  have hdb : d ≤ 2 * (5 * d) := by omega
  have hsum := sum_saksZhouBaseCounts_le M hd B p.2
  dsimp only [saksZhouEntryLoop]
  rw [nisanSweepLoop_run (a := p) (hdb := hdb)]
  · let levels := saksZhouLevels clk p.2.length
    let b := 2 * (5 * d)
    let z := nisanShiftSeedOfNat b levels levels d p.1.seed
    exact clamp_entry n p.1.row p.1.column (nisanSnapCounts (Equiv.refl _) b d levels z.1
      (saksZhouBaseCounts M d B p.2) levels z.2)
  · exact hsum

/-- The reply to every recursive job fits the precision, including out-of-bounds marker jobs. -/
theorem saksZhouEntryLoop_run_le (c clk : ℕ) (p : SaksZhouEntry × List Bool) (level : ℕ)
    (q : SweepJob) :
    (saksZhouEntryLoop M c clk).run p level q ≤ 2 ^ saksZhouPrecision clk p.2.length := by
  dsimp only [saksZhouEntryLoop]
  apply nisanSweepLoop_run_le
  · omega
  · exact sum_saksZhouBaseCounts_le M (by simp only [saksZhouPrecision]; omega) _ _

end Turing.MultiTapePTM.ConfigurationGraph
