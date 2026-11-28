/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Input
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Workspace layout, fitting lemmas, and initialized arborescence memory (internal)

Defines base offsets (`curAdjBase`, …, `frameRepAddr`, `wsSize`), `WsFits`, word-bound fitting
lemmas, and initial memory lemmas for `ArborescenceInput.encode`.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

public theorem sq_le_wordBound (n M₀ : ℕ) : 32 * (n + 1) * (n + 1) ≤ wordBound n M₀ := by
  have h : 32 * (n + 1) * (n + 1) = 32 * (n + 1) ^ 2 := by ring
  unfold wordBound
  omega

public theorem fits_signedEncode_add_one_of_wordBound {w n M₀ : ℕ} {z : ℤ}
    (hz : z.natAbs ≤ M₀) (hwb : Fits w (wordBound n M₀)) :
    Fits w (Signed.encode z + 1) := by
  have hmul : 2 * z.natAbs ≤ 4 * (n + 1) * M₀ := by nlinarith only [hz]
  have hsq1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos _)
  unfold Signed.encode
  exact hwb.of_le (by dsimp only [wordBound]; split_ifs <;> linarith only [hmul, hsq1])

/-- Word-pair encoding of two `ℕ` values into two words. -/
public abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  appendWords wordWords wordWords

/-! ### Workspace layout -/

/-- Base address of the active working `n × n` adjacency table in the workspace. -/
public abbrev curAdjBase (ws _n : ℕ) : ℕ := ws
/-- Base address of the active working `n × n` signed cost table in the workspace. -/
public abbrev curCostBase (ws n : ℕ) : ℕ := ws + n * n
/-- Base address of the scratch `n × n` adjacency table used during contraction. -/
public abbrev nextAdjBase (ws n : ℕ) : ℕ := ws + 2 * (n * n)
/-- Base address of the scratch `n × n` signed cost table used during contraction. -/
public abbrev nextCostBase (ws n : ℕ) : ℕ := ws + 3 * (n * n)
/-- Base address of the `n`-word candidate feasibility mask array for argmin scans. -/
public abbrev candPredBase (ws n : ℕ) : ℕ := ws + 4 * (n * n)
/-- Base address of the `n`-word candidate cost array for argmin scans. -/
public abbrev candCostBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + n
/-- Base address of the active `n`-word parent array in the workspace. -/
public abbrev curParentBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + 2 * n
/-- Base address of the scratch `n`-word parent array used during expansion. -/
public abbrev nextParentBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + 3 * n
/-- Base address of contraction stack frame `k` (size `4 * n + 1` words). -/
public abbrev frameBase (ws n k : ℕ) : ℕ := ws + 4 * (n * n) + 4 * n + k * (4 * n + 1)
/-- Base address of frame `k`'s selected `n`-word parent table. -/
public abbrev frameParentBase (ws n k : ℕ) : ℕ := frameBase ws n k
/-- Base address of frame `k`'s `n`-word contracted-cycle membership mask. -/
public abbrev frameMaskBase (ws n k : ℕ) : ℕ := frameBase ws n k + n
/-- Base address of frame `k`'s `n`-word best-entry vertex array. -/
public abbrev frameBEntryBase (ws n k : ℕ) : ℕ := frameBase ws n k + 2 * n
/-- Base address of frame `k`'s `n`-word best-exit vertex array. -/
public abbrev frameBExitBase (ws n k : ℕ) : ℕ := frameBase ws n k + 3 * n
/-- Address storing frame `k`'s cycle representative vertex. -/
public abbrev frameRepAddr (ws n k : ℕ) : ℕ := frameBase ws n k + 4 * n
/-- Total word footprint of the dense Chu–Liu/Edmonds workspace for `n` vertices. -/
public abbrev wsSize (n : ℕ) : ℕ := 4 * (n * n) + 4 * n + n * (4 * n + 1)

/-- Uniform address-fit predicate covering all workspace offsets and small constants. -/
public abbrev WsFits (w ws n : ℕ) : Prop :=
  Fits w (ws + wsSize n + 8)

public theorem frame_le_frames {n k : ℕ} (hk : k < n) :
    k * (4 * n + 1) + (4 * n + 1) ≤ n * (4 * n + 1) := by
  simpa [Nat.succ_mul] using Nat.mul_le_mul_right (4 * n + 1) hk

public theorem init_mem_encode_arb_adj (I : ArborescenceInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (3 + (u.val * I.n + v.val)) = if I.adj u v then 1 else 0 := by
  rw [show 3 + (u.val * I.n + v.val) = ((u.val * I.n + v.val) + 2) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((u.val * I.n + v.val) + 2) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [ArborescenceInput.encode]
  rw [List.getD_cons_succ, List.getD_cons_succ]
  have hlt : u.val * I.n + v.val < (flattenBoolMatrix I.n I.adj).length := by
    rw [length_flattenBoolMatrix]; exact List.mul_add_lt_sq u.isLt v.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  exact getD_flattenBoolMatrix I.n I.adj u v

public theorem init_mem_encode_arb_cost (I : ArborescenceInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (3 + I.n * I.n + (u.val * I.n + v.val)) =
      Signed.encode (I.cost u v) := by
  rw [show 3 + I.n * I.n + (u.val * I.n + v.val) =
    ((I.n * I.n + (u.val * I.n + v.val)) + 2) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((I.n * I.n + (u.val * I.n + v.val)) + 2) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [ArborescenceInput.encode]
  rw [List.getD_cons_succ, List.getD_cons_succ]
  have hlen1 : (flattenBoolMatrix I.n I.adj).length = I.n * I.n :=
    length_flattenBoolMatrix I.n I.adj
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
  simp only [hlen1, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact getD_flattenSignedMatrix I.n I.cost u v

public theorem fits_mem_flatten_adj_signed {w n m M₀ : ℕ}
    (adj : Fin n → Fin n → Bool) (wt : Fin n → Fin n → ℤ)
    (hM : ∀ u v, (wt u v).natAbs ≤ M₀) (hwb : Fits w (wordBound m M₀))
    {x : ℕ} (hx : x ∈ flattenBoolMatrix n adj ++ flattenSignedMatrix n wt) :
    Fits w x := by
  have hsq := sq_le_wordBound m M₀
  rcases List.mem_append.mp hx with hbool | hwt
  · simp only [flattenBoolMatrix, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and] at hbool
    rcases hbool with ⟨u, v, rfl⟩
    split_ifs <;> exact hwb.of_le (by nlinarith only [hsq])
  · simp only [flattenSignedMatrix, List.mem_flatMap, List.mem_finRange, List.mem_map,
      true_and] at hwt
    rcases hwt with ⟨u, v, rfl⟩
    exact (fits_signedEncode_add_one_of_wordBound (hM u v) hwb).of_le (Nat.le_succ _)

public theorem inputFits_arb_encode {w M₀ : ℕ} (I : ArborescenceInput)
    (hM : ∀ u v, (I.cost u v).natAbs ≤ M₀) (hwb : Fits w (wordBound I.n M₀)) :
    Fits w (I.encode.length + 1) ∧ InputFits w I.encode := by
  have hsq := sq_le_wordBound I.n M₀
  have hlen : I.encode.length = 2 + 2 * (I.n * I.n) := by
    simp [ArborescenceInput.encode, length_flattenBoolMatrix, length_flattenSignedMatrix]
    omega
  have hfit_len1 : Fits w (I.encode.length + 1) :=
    hwb.of_le (by rw [hlen]; nlinarith only [hsq])
  refine ⟨hfit_len1, hfit_len1.of_le (by omega), fun x hx => ?_⟩
  simp only [ArborescenceInput.encode, List.mem_cons] at hx
  rcases hx with rfl | rfl | hrest
  · exact hwb.of_le (by nlinarith only [hsq])
  · exact hwb.of_le (by have hr := I.root.isLt; nlinarith only [hsq, hr])
  · exact fits_mem_flatten_adj_signed I.adj I.cost hM hwb hrest

end Cslib.Algorithms.WordRAM.Arborescence.Internal
