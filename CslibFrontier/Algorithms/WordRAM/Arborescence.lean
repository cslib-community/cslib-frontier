/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Branching
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Algorithms.Lean.Arborescence.Table
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.Signed
import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.DataStructure.StateTransition
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize

/-!
# Materialized-table Chu–Liu/Edmonds and optimum branchings on the Word-RAM (`O(n³)`)

This module implements a dense materialized-table Chu–Liu/Edmonds minimum-cost spanning
arborescence algorithm and this formalization's super-root maximum-weight branching reduction on
the deterministic standard-basis Word-RAM (`Cslib.WordRAM.Basis.standard`), proving uniform
width-blind (`¬prog.ReadsWidth`) instruction-count bounds `C * (I.n + 1) ^ 3`
(`Program.ComputesListInTime`) at every word width `w` satisfying `Fits w I.wordBound` (i.e.,
`I.wordBound < 2 ^ w`). Because `wordBound n M₀ = 4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2` is a
polynomial bound on **word values and addresses**, a word width `w` of order
`log(n + 2) + log(M₀ + 2)` bits suffices.

Signed integer arc costs and weights are represented in memory via `Cslib.WordRAM.Signed.encode`
(`2 * |z| + signBit`). In [Edmonds1967Branchings], §4 instruction (I2), equation (1), contracting a
cycle adjusts the weight of each arc entering the cycle by subtracting its selected cycle-edge
weight and adding a cycle-wide offset. This module implements the rooted, reversed min-cost
variant: at round `k`, the contracted exit cost for an arc `(x, w)` leaving a contracted cycle `C`
(`x ∈ C`, `w ∉ C`) is computed as the reduced exit-cost difference `c_k[x][w] - c_k[x][f[x]]` (with
inactive contracted cells set to `0`). Because `f[x]` minimizes `c_k[x][z]` over active non-self
outgoing arcs of `x`, every reduced exit cost is nonnegative (`0 ≤ c_k[x][w] - c_k[x][f[x]]`), so
all entries of the working cost matrix stay within `[-M₀, (k + 1) * M₀]` across all `k ≤ n`
contraction rounds while maintaining exact row-potential equivalence (`∃ φ, ∀ u w, a[u][w] →
c_unred[u][w] = c_red[u][w] + φ u`) with `edmondsTableAux`. Consequently, any word width `w`
satisfying `Fits w (wordBound n M₀)` (`wordBound n M₀ < 2 ^ w`, so `w` of order
`log(n + 2) + log(M₀ + 2)` bits) accommodates all signed-encoded intermediate weights and `O(n²)`
workspace addresses without overflow.

For maximum-weight branchings, [Edmonds1967Branchings], §2 adds a new node with one arc to a
prescribed root and reduces optimum spanning arborescence to optimum branching via a weight shift
(formalized in `CslibFrontier.Algorithms.Lean.Arborescence.Branching`). To solve maximum-weight
branchings via the rooted in-arborescence Word-RAM core, `optimumBranchingProg` implements this
formalization's reverse super-root reduction from
`CslibFrontier.Algorithms.Lean.Arborescence.Branching`: it reduces maximum-weight branching to
rooted spanning in-arborescence by adding a zero-cost arc from every original vertex to the
super-root and reversing and negating all original arcs.

The dense `O(n³)` Word-RAM realization, workspace layout, word-value/address bound, and
instruction-count bounds are original to this formalization over the cycle-contraction algorithm
and §2 weight-shift reduction of [Edmonds1967Branchings], Sections 1–4 ([ChuLiu1965] was not
inspected directly).

## Main definitions

* `Cslib.Algorithms.WordRAM.Arborescence.wordBound`: polynomial bound
  `4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2` on word values and workspace addresses; `Fits w (wordBound
  n M₀)` (`wordBound n M₀ < 2 ^ w`) holds at word widths `w` of order `log(n + 2) + log(M₀ + 2)`
  bits.
* `Cslib.Algorithms.WordRAM.Arborescence.flattenBoolMatrix`,
  `Cslib.Algorithms.WordRAM.Arborescence.flattenSignedMatrix`: row-major flat word-list encodings
  of Boolean adjacency and signed cost/weight matrices.
* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput`: weighted digraph inputs on `Fin n` with
  intrinsic magnitude and word-value/address bounds (`maxAbsCost`, `maxAbsWeight`, `wordBound`),
  flat word encodings (`encode`), and expected parent-list outputs (`expectedParentList`,
  `expectedOutParentList`).

## Main results

* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput.expectedParentList_spec`: public
  correctness and optimality characterizations of the encoded parent-list outputs.
* `Cslib.Algorithms.WordRAM.Arborescence.exists_edmonds_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for Chu–Liu/Edmonds minimum-cost
  spanning in-arborescence running in `C * (I.n + 1) ^ 3` instructions at every word width `w`
  satisfying `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).
* `Cslib.Algorithms.WordRAM.Arborescence.exists_edmondsOut_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for minimum-cost spanning
  out-arborescence running in `C * (I.n + 1) ^ 3` instructions at every word width `w` satisfying
  `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).
* `Cslib.Algorithms.WordRAM.Arborescence.exists_optimumBranching_program`: uniform width-blind
  standard-basis Word-RAM program (`Program.ComputesListInTime`) for maximum-weight branching via
  this formalization's super-root reduction, running in `C * (I.n + 1) ^ 3` instructions at every
  word width `w` satisfying `Fits w I.wordBound` (`I.wordBound < 2 ^ w`).

## References

* [J. Edmonds, *Optimum branchings*][Edmonds1967Branchings], Sections 1–4
-/

namespace Cslib.Algorithms.WordRAM.Arborescence

open Cslib.Algorithms.Lean.Arborescence
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

-- Local `simp`-indexed forms matching `StateTransitionSpec.fst_snd_runClient_bind`.
@[local client_simps] private theorem local_fst_snd_read (w : ℕ) (s : Memory.State) (a : ℕ) :
    ((Memory.spec w).runClient s (Memory.read a)).2.1 = s := by
  rw [runClient_read]

@[local client_simps] private theorem local_fst_snd_write (w : ℕ) (s : Memory.State) (a v : ℕ) :
    ((Memory.spec w).runClient s (Memory.write a v)).2.1 =
      ⟨Function.update s.mem a v, s.frontier⟩ := by
  rw [runClient_write]

@[local client_simps] private theorem local_fst_snd_allocDirty (w : ℕ) (s : Memory.State) (k : ℕ) :
    ((Memory.spec w).runClient s (Memory.allocDirty k)).2.1 = ⟨s.mem, s.frontier + k⟩ := by
  rw [runClient_allocDirty]

@[local client_simps] private theorem local_fst_snd_map {α β : Type} (w : ℕ)
    (s : Memory.State) (g : α → β) (p : Memory.Prog α) :
    ((Memory.spec w).runClient s (g <$> p : Memory.Prog β)).2.1 =
      (Memory.spec w).clientState s p := by
  rw [runClient_map]

@[local client_simps] private theorem local_fst_snd_ite {α : Type} (w : ℕ)
    (c : Prop) [Decidable c] (p₁ p₂ : Memory.Prog α) (s : Memory.State) :
    ((Memory.spec w).runClient s (if c then p₁ else p₂ : Memory.Prog α)).2.1 =
      if c then (Memory.spec w).clientState s p₁ else (Memory.spec w).clientState s p₂ := by
  rw [runClient_ite]; split_ifs <;> rfl

@[local client_simps] private theorem local_fst_snd_signedNegProg (w : ℕ)
    (s : Memory.State) (u : ℕ) :
    ((Memory.spec w).runClient s (signedNegProg u)).2.1 = s :=
  clientState_signedNegProg s u

@[local client_simps] private theorem local_fst_snd_signedSubProg (w : ℕ)
    (s : Memory.State) (d : ℕ × ℕ) :
    ((Memory.spec w).runClient s (signedSubProg d)).2.1 = s :=
  clientState_signedSubProg s d

/-! ### Word-value and address bound -/

public section

/-- Polynomial bound on word values and workspace addresses covering the rooted, reversed min-cost
reduced exit costs up to `4 * (n + 1) * M₀` together with all `O(n²)` workspace addresses.
The condition `Fits w (wordBound n M₀)` means `wordBound n M₀ < 2 ^ w`, so a word width `w` of
order `log(n + 2) + log(M₀ + 2)` bits suffices. -/
@[expose] def wordBound (n M₀ : ℕ) : ℕ :=
  4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2

end

private theorem sq_le_wordBound (n M₀ : ℕ) : 32 * (n + 1) * (n + 1) ≤ wordBound n M₀ := by
  have h : 32 * (n + 1) * (n + 1) = 32 * (n + 1) ^ 2 := by ring
  unfold wordBound
  omega

private theorem fits_signedEncode_add_one_of_wordBound {w n M₀ : ℕ} {z : ℤ}
    (hz : z.natAbs ≤ M₀) (hwb : Fits w (wordBound n M₀)) :
    Fits w (Signed.encode z + 1) := by
  have hmul : 2 * z.natAbs ≤ 4 * (n + 1) * M₀ := by nlinarith only [hz]
  have hsq1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos _)
  unfold Signed.encode
  exact hwb.of_le (by dsimp only [wordBound]; split_ifs <;> linarith only [hmul, hsq1])

private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  appendWords wordWords wordWords

/-! ### Workspace layout -/

private abbrev curAdjBase (ws _n : ℕ) : ℕ := ws
private abbrev curCostBase (ws n : ℕ) : ℕ := ws + n * n
private abbrev nextAdjBase (ws n : ℕ) : ℕ := ws + 2 * (n * n)
private abbrev nextCostBase (ws n : ℕ) : ℕ := ws + 3 * (n * n)
private abbrev candPredBase (ws n : ℕ) : ℕ := ws + 4 * (n * n)
private abbrev candCostBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + n
private abbrev curParentBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + 2 * n
private abbrev nextParentBase (ws n : ℕ) : ℕ := ws + 4 * (n * n) + 3 * n
private abbrev frameBase (ws n k : ℕ) : ℕ := ws + 4 * (n * n) + 4 * n + k * (4 * n + 1)
private abbrev frameParentBase (ws n k : ℕ) : ℕ := frameBase ws n k
private abbrev frameMaskBase (ws n k : ℕ) : ℕ := frameBase ws n k + n
private abbrev frameBEntryBase (ws n k : ℕ) : ℕ := frameBase ws n k + 2 * n
private abbrev frameBExitBase (ws n k : ℕ) : ℕ := frameBase ws n k + 3 * n
private abbrev frameRepAddr (ws n k : ℕ) : ℕ := frameBase ws n k + 4 * n
private abbrev wsSize (n : ℕ) : ℕ := 4 * (n * n) + 4 * n + n * (4 * n + 1)

/-- Uniform address-fit predicate covering all workspace offsets and small constants. -/
private abbrev WsFits (w ws n : ℕ) : Prop :=
  Fits w (ws + wsSize n + 8)

private theorem frame_le_frames {n k : ℕ} (hk : k < n) :
    k * (4 * n + 1) + (4 * n + 1) ≤ n * (4 * n + 1) := by
  simpa [Nat.succ_mul] using Nat.mul_le_mul_right (4 * n + 1) hk

/-! ### Subroutines and `Realizes` certificates -/

-- 1. `copyWordsProg` and `zeroWordsProg`

private structure CopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private word_enc_structure encCopyArgs : CopyArgs where
  src : wordWords, dst : wordWords, len : wordWords

private instance : WordEncoding CopyArgs := ⟨3, encCopyArgs⟩

private def copyStep (x : CopyArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  let v ← Memory.read (env.src + i)
  Memory.write (env.dst + i) v
  pure (i + 1)

private abbrev CopyStepSafe (w : ℕ) (x : CopyArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let i := Prod.snd x
  Fits w (env.src + i) ∧ Fits w (env.dst + i) ∧ Fits w (i + 1)

private theorem copyStep_realizes :
    Realizes .exact copyStep (appendWords encCopyArgs wordWords) wordWords
      CopyStepSafe (fun _ _ => 0) := by
  unfold copyStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def copyWordsProg (a : CopyArgs) : Memory.Prog ℕ :=
  iterate copyStep a a.len 0

private theorem copyWordsProg_realizes :
    Realizes .exact copyWordsProg encCopyArgs wordWords
      (fun w a s => iterationSafe copyStep CopyStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold copyWordsProg
  realize [copyStep_realizes]
  exact h

private structure ZeroArgs where
  dst : ℕ
  len : ℕ

private word_enc_structure encZeroArgs : ZeroArgs where
  dst : wordWords, len : wordWords

private instance : WordEncoding ZeroArgs := ⟨2, encZeroArgs⟩

private def zeroStep (x : ZeroArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  Memory.write (env.dst + i) 0
  pure (i + 1)

private abbrev ZeroStepSafe (w : ℕ) (x : ZeroArgs × ℕ) (_ : Memory.State) : Prop :=
  Fits w ((Prod.fst x).dst + Prod.snd x) ∧ Fits w (Prod.snd x + 1)

private theorem zeroStep_realizes :
    Realizes .exact zeroStep (appendWords encZeroArgs wordWords) wordWords
      ZeroStepSafe (fun _ _ => 0) := by
  unfold zeroStep
  realize
  all_goals first | exact h.1 | exact h.2

private def zeroWordsProg (a : ZeroArgs) : Memory.Prog ℕ :=
  iterate zeroStep a a.len 0

private theorem zeroWordsProg_realizes :
    Realizes .exact zeroWordsProg encZeroArgs wordWords
      (fun w a s => iterationSafe zeroStep ZeroStepSafe w a a.len 0 s)
      (fun _ _ => 0) := by
  unfold zeroWordsProg
  realize [zeroStep_realizes]
  exact h

-- 2. `argMinArrayProg`

private structure ArgMinArgs where
  n : ℕ
  predBase : ℕ
  costBase : ℕ

private word_enc_structure encArgMinArgs : ArgMinArgs where
  n : wordWords, predBase : wordWords, costBase : wordWords

private instance : WordEncoding ArgMinArgs := ⟨3, encArgMinArgs⟩

private structure ArgMinState where
  idx : ℕ
  bestIdx : ℕ
  bestCost : ℕ

private word_enc_structure encArgMinState : ArgMinState where
  idx : wordWords, bestIdx : wordWords, bestCost : wordWords

private instance : WordEncoding ArgMinState := ⟨3, encArgMinState⟩

private def argMinStep (x : ArgMinArgs × ArgMinState) : Memory.Prog ArgMinState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let p ← Memory.read (env.predBase + st.idx)
  let c ← Memory.read (env.costBase + st.idx)
  if p = 1 then
    if st.bestIdx = env.n then
      pure ⟨st.idx + 1, st.idx, c⟩
    else if SignedLtWord c st.bestCost then
      pure ⟨st.idx + 1, st.idx, c⟩
    else
      pure ⟨st.idx + 1, st.bestIdx, st.bestCost⟩
  else
    pure ⟨st.idx + 1, st.bestIdx, st.bestCost⟩

private abbrev ArgMinStepSafe (w : ℕ) (x : ArgMinArgs × ArgMinState) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 2 ∧ Fits w (env.predBase + st.idx) ∧ Fits w (env.costBase + st.idx) ∧ Fits w (st.idx + 1)

private theorem argMinStep_realizes :
    Realizes .exact argMinStep (appendWords encArgMinArgs encArgMinState) encArgMinState
      ArgMinStepSafe (fun _ _ => 0) := by
  unfold argMinStep
  realize
  all_goals
    first | omega | exact h.1.of_le (by omega) | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2

private def argMinArrayProg (a : ArgMinArgs) : Memory.Prog ℕ := do
  let res ← iterate argMinStep a a.n ⟨0, a.n, 0⟩
  pure res.bestIdx

private theorem argMinArrayProg_realizes :
    Realizes .exact argMinArrayProg encArgMinArgs wordWords
      (fun w a s => iterationSafe argMinStep ArgMinStepSafe w a a.n ⟨0, a.n, 0⟩ s)
      (fun _ _ => 0) := by
  unfold argMinArrayProg
  realize [argMinStep_realizes]
  exact h

-- 3. `selectParentsProg`

private structure SelectRowArgs where
  n : ℕ
  v : ℕ
  adjBase : ℕ
  costBase : ℕ
  predOut : ℕ
  costOut : ℕ

private word_enc_structure encSelectRowArgs : SelectRowArgs where
  n : wordWords, v : wordWords, adjBase : wordWords, costBase : wordWords,
  predOut : wordWords, costOut : wordWords

private instance : WordEncoding SelectRowArgs := ⟨6, encSelectRowArgs⟩

private def selectRowStep (x : SelectRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let col := Prod.snd x
  let avw ← Memory.read (env.adjBase + env.v * env.n + col)
  let cvw ← Memory.read (env.costBase + env.v * env.n + col)
  let pv := if avw = 1 ∧ col ≠ env.v then 1 else 0
  Memory.write (env.predOut + col) pv
  Memory.write (env.costOut + col) cvw
  pure (col + 1)

private abbrev SelectRowStepSafe (w : ℕ) (x : SelectRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let col := Prod.snd x
  Fits w 1 ∧ Fits w (env.adjBase + env.v * env.n + col) ∧
    Fits w (env.costBase + env.v * env.n + col) ∧
    Fits w (env.predOut + col) ∧ Fits w (env.costOut + col) ∧ Fits w (col + 1)

private theorem selectRowStep_realizes :
    Realizes .exact selectRowStep (appendWords encSelectRowArgs wordWords) wordWords
      SelectRowStepSafe (fun _ _ => 0) := by
  unfold selectRowStep
  realize
  all_goals
    obtain ⟨h1, ha, hc, hp, hco, hi⟩ := h
    first | exact h1 | exact ha | exact hc | exact hp | exact hco | exact hi

private def fillSelectRowProg (a : SelectRowArgs) : Memory.Prog ℕ :=
  iterate selectRowStep a a.n 0

private theorem fillSelectRowProg_realizes :
    Realizes .exact fillSelectRowProg encSelectRowArgs wordWords
      (fun w a s => iterationSafe selectRowStep SelectRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillSelectRowProg
  realize [selectRowStep_realizes]
  exact h

private structure SelectArgs where
  n : ℕ
  r : ℕ
  ws : ℕ
  k : ℕ

private word_enc_structure encSelectArgs : SelectArgs where
  n : wordWords, r : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding SelectArgs := ⟨4, encSelectArgs⟩

private structure SelectState where
  v : ℕ
  feas : ℕ

private word_enc_structure encSelectState : SelectState where
  v : wordWords, feas : wordWords

private instance : WordEncoding SelectState := ⟨2, encSelectState⟩

private def selectOuterStep (x : SelectArgs × SelectState) : Memory.Prog SelectState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let _ ← Memory.read 0
  let pBase := frameParentBase env.ws env.n env.k
  if st.v = env.r then
    Memory.write (pBase + st.v) env.r
    pure ⟨st.v + 1, st.feas⟩
  else
    let rowArgs : SelectRowArgs :=
      ⟨env.n, st.v, curAdjBase env.ws env.n, curCostBase env.ws env.n,
        candPredBase env.ws env.n, candCostBase env.ws env.n⟩
    let _ ← fillSelectRowProg rowArgs
    let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
    if best < env.n then
      Memory.write (pBase + st.v) best
      pure ⟨st.v + 1, st.feas⟩
    else
      Memory.write (pBase + st.v) st.v
      pure ⟨st.v + 1, 0⟩

private abbrev SelectOuterStepSafe (w : ℕ) (x : SelectArgs × SelectState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let rowArgs : SelectRowArgs :=
    ⟨env.n, st.v, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
  st.v < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe selectRowStep SelectRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem selectOuterStep_realizes :
    Realizes .exact selectOuterStep (appendWords encSelectArgs encSelectState) encSelectState
      SelectOuterStepSafe (fun _ _ => 0) := by
  unfold selectOuterStep
  realize [fillSelectRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hv, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameBase, curAdjBase, curCostBase,
          candPredBase, candCostBase]
        nlinarith)

private def selectParentsProg (a : SelectArgs) : Memory.Prog ℕ := do
  let res ← iterate selectOuterStep a a.n ⟨0, 1⟩
  pure res.feas

private theorem selectParentsProg_realizes :
    Realizes .exact selectParentsProg encSelectArgs wordWords
      (fun w a s => Fits w 1 ∧
        iterationSafe selectOuterStep SelectOuterStepSafe w a a.n ⟨0, 1⟩ s)
      (fun _ _ => 0) := by
  unfold selectParentsProg
  realize [selectOuterStep_realizes]
  all_goals first | exact h.1 | exact h.2

-- 4. `hasCycleFromProg` and `findCycleProg`

private structure HasCycleArgs where
  n : ℕ
  parentBase : ℕ
  start : ℕ

private word_enc_structure encHasCycleArgs : HasCycleArgs where
  n : wordWords, parentBase : wordWords, start : wordWords

private instance : WordEncoding HasCycleArgs := ⟨3, encHasCycleArgs⟩

private structure HasCycleState where
  step : ℕ
  cur : ℕ
  hit : ℕ

private word_enc_structure encHasCycleState : HasCycleState where
  step : wordWords, cur : wordWords, hit : wordWords

private instance : WordEncoding HasCycleState := ⟨3, encHasCycleState⟩

private def hasCycleStep (x : HasCycleArgs × HasCycleState) : Memory.Prog HasCycleState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let nxt ← Memory.read (env.parentBase + st.cur)
  if st.hit = 1 ∨ nxt = env.start then
    pure ⟨st.step + 1, nxt, 1⟩
  else
    pure ⟨st.step + 1, nxt, 0⟩

private abbrev HasCycleStepSafe (w : ℕ) (x : HasCycleArgs × HasCycleState)
    (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (env.parentBase + st.cur) ∧ Fits w (st.step + 1)

private theorem hasCycleStep_realizes :
    Realizes .exact hasCycleStep (appendWords encHasCycleArgs encHasCycleState) encHasCycleState
      HasCycleStepSafe (fun _ _ => 0) := by
  unfold hasCycleStep
  realize
  all_goals
    obtain ⟨h1, hp, hs⟩ := h
    first | exact h1 | exact hp | exact hs

private def hasCycleFromProg (a : HasCycleArgs) : Memory.Prog ℕ := do
  let res ← iterate hasCycleStep a a.n ⟨0, a.start, 0⟩
  pure res.hit

private theorem hasCycleFromProg_realizes :
    Realizes .exact hasCycleFromProg encHasCycleArgs wordWords
      (fun w a s => iterationSafe hasCycleStep HasCycleStepSafe w a a.n ⟨0, a.start, 0⟩ s)
      (fun _ _ => 0) := by
  unfold hasCycleFromProg
  realize [hasCycleStep_realizes]
  exact h

private structure FindCycleArgs where
  n : ℕ
  r : ℕ
  parentBase : ℕ

private word_enc_structure encFindCycleArgs : FindCycleArgs where
  n : wordWords, r : wordWords, parentBase : wordWords

private instance : WordEncoding FindCycleArgs := ⟨3, encFindCycleArgs⟩

private structure FindCycleState where
  v : ℕ
  found : ℕ

private word_enc_structure encFindCycleState : FindCycleState where
  v : wordWords, found : wordWords

private instance : WordEncoding FindCycleState := ⟨2, encFindCycleState⟩

private def findCycleOuterStep (x : FindCycleArgs × FindCycleState) :
    Memory.Prog FindCycleState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let _ ← Memory.read 0
  if st.found < env.n then
    pure ⟨st.v + 1, st.found⟩
  else if st.v = env.r then
    pure ⟨st.v + 1, env.n⟩
  else
    let hit ← hasCycleFromProg ⟨env.n, env.parentBase, st.v⟩
    if hit = 1 then
      pure ⟨st.v + 1, st.v⟩
    else
      pure ⟨st.v + 1, env.n⟩

private abbrev FindCycleOuterStepSafe (w : ℕ) (x : FindCycleArgs × FindCycleState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (st.v + 1) ∧
    iterationSafe hasCycleStep HasCycleStepSafe w ⟨env.n, env.parentBase, st.v⟩ env.n
      ⟨0, st.v, 0⟩ s

private theorem findCycleOuterStep_realizes :
    Realizes .exact findCycleOuterStep (appendWords encFindCycleArgs encFindCycleState)
      encFindCycleState FindCycleOuterStepSafe (fun _ _ => 0) := by
  unfold findCycleOuterStep
  realize [hasCycleFromProg_realizes]
  all_goals
    obtain ⟨h1, hv, hcyc⟩ := h
    first | exact h1 | exact hv | exact hcyc

private def findCycleProg (a : FindCycleArgs) : Memory.Prog ℕ := do
  let res ← iterate findCycleOuterStep a a.n ⟨0, a.n⟩
  pure res.found

private theorem findCycleProg_realizes :
    Realizes .exact findCycleProg encFindCycleArgs wordWords
      (fun w a s => iterationSafe findCycleOuterStep FindCycleOuterStepSafe w a a.n ⟨0, a.n⟩ s)
      (fun _ _ => 0) := by
  unfold findCycleProg
  realize [findCycleOuterStep_realizes]
  exact h

-- 5. `cycleMaskProg`

private structure CycleMaskArgs where
  n : ℕ
  parentBase : ℕ
  maskBase : ℕ
  x0 : ℕ

private word_enc_structure encCycleMaskArgs : CycleMaskArgs where
  n : wordWords, parentBase : wordWords, maskBase : wordWords, x0 : wordWords

private instance : WordEncoding CycleMaskArgs := ⟨4, encCycleMaskArgs⟩

private structure CycleMaskState where
  step : ℕ
  cur : ℕ

private word_enc_structure encCycleMaskState : CycleMaskState where
  step : wordWords, cur : wordWords

private instance : WordEncoding CycleMaskState := ⟨2, encCycleMaskState⟩

private def cycleMaskStep (x : CycleMaskArgs × CycleMaskState) : Memory.Prog CycleMaskState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let nxt ← Memory.read (env.parentBase + st.cur)
  Memory.write (env.maskBase + st.cur) 1
  pure ⟨st.step + 1, nxt⟩

private abbrev CycleMaskStepSafe (w : ℕ) (x : CycleMaskArgs × CycleMaskState)
    (_ : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  Fits w 1 ∧ Fits w (env.parentBase + st.cur) ∧
    Fits w (env.maskBase + st.cur) ∧ Fits w (st.step + 1)

private theorem cycleMaskStep_realizes :
    Realizes .exact cycleMaskStep (appendWords encCycleMaskArgs encCycleMaskState)
      encCycleMaskState CycleMaskStepSafe (fun _ _ => 0) := by
  unfold cycleMaskStep
  realize
  all_goals
    obtain ⟨h1, hp, hm, hs⟩ := h
    first | exact h1 | exact hp | exact hm | exact hs

private def cycleMaskLoopProg (a : CycleMaskArgs) : Memory.Prog ℕ := do
  let res ← iterate cycleMaskStep a a.n ⟨0, a.x0⟩
  pure res.step

private theorem cycleMaskLoopProg_realizes :
    Realizes .exact cycleMaskLoopProg encCycleMaskArgs wordWords
      (fun w a s => iterationSafe cycleMaskStep CycleMaskStepSafe w a a.n ⟨0, a.x0⟩ s)
      (fun _ _ => 0) := by
  unfold cycleMaskLoopProg
  realize [cycleMaskStep_realizes]
  exact h

private def cycleMaskProg (a : CycleMaskArgs) : Memory.Prog ℕ := do
  let _ ← zeroWordsProg ⟨a.maskBase, a.n⟩
  cycleMaskLoopProg a

private theorem cycleMaskProg_realizes :
    Realizes .exact cycleMaskProg encCycleMaskArgs wordWords
      (fun w a s =>
        let s1 := (Memory.spec 0).clientState s (zeroWordsProg ⟨a.maskBase, a.n⟩)
        iterationSafe zeroStep ZeroStepSafe w ⟨a.maskBase, a.n⟩ a.n 0 s ∧
          iterationSafe cycleMaskStep CycleMaskStepSafe w a a.n ⟨0, a.x0⟩ s1)
      (fun _ _ => 0) := by
  unfold cycleMaskProg
  realize [zeroWordsProg_realizes, cycleMaskLoopProg_realizes]
  all_goals first | exact h.1 | exact h.2

-- 6. `bestEntryProg` and `bestExitProg` (with Edmonds §4 reduced exit costs)

private structure BestEntryRowArgs where
  n : ℕ
  u : ℕ
  adjBase : ℕ
  costBase : ℕ
  maskBase : ℕ
  predOut : ℕ
  costOut : ℕ

private word_enc_structure encBestEntryRowArgs : BestEntryRowArgs where
  n : wordWords, u : wordWords, adjBase : wordWords, costBase : wordWords,
  maskBase : wordWords, predOut : wordWords, costOut : wordWords

private instance : WordEncoding BestEntryRowArgs := ⟨7, encBestEntryRowArgs⟩

private def bestEntryRowStep (q : BestEntryRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let y := Prod.snd q
  let inY ← Memory.read (env.maskBase + y)
  let auy ← Memory.read (env.adjBase + env.u * env.n + y)
  let cuy ← Memory.read (env.costBase + env.u * env.n + y)
  let pv := if inY = 1 ∧ auy = 1 then 1 else 0
  Memory.write (env.predOut + y) pv
  Memory.write (env.costOut + y) cuy
  pure (y + 1)

private abbrev BestEntryRowStepSafe (w : ℕ) (q : BestEntryRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let y := Prod.snd q
  Fits w 1 ∧ Fits w (env.maskBase + y) ∧ Fits w (env.adjBase + env.u * env.n + y) ∧
    Fits w (env.costBase + env.u * env.n + y) ∧ Fits w (env.predOut + y) ∧
    Fits w (env.costOut + y) ∧ Fits w (y + 1)

private theorem bestEntryRowStep_realizes :
    Realizes .exact bestEntryRowStep (appendWords encBestEntryRowArgs wordWords) wordWords
      BestEntryRowStepSafe (fun _ _ => 0) := by
  unfold bestEntryRowStep
  realize
  all_goals
    obtain ⟨h1, hm, ha, hc, hp, hco, hy⟩ := h
    first | exact h1 | exact hm | exact ha | exact hc | exact hp | exact hco | exact hy

private def fillBestEntryRowProg (a : BestEntryRowArgs) : Memory.Prog ℕ :=
  iterate bestEntryRowStep a a.n 0

private theorem fillBestEntryRowProg_realizes :
    Realizes .exact fillBestEntryRowProg encBestEntryRowArgs wordWords
      (fun w a s => iterationSafe bestEntryRowStep BestEntryRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillBestEntryRowProg
  realize [bestEntryRowStep_realizes]
  exact h

private structure LevelArgs where
  n : ℕ
  ws : ℕ
  k : ℕ

private word_enc_structure encLevelArgs : LevelArgs where
  n : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding LevelArgs := ⟨3, encLevelArgs⟩

private def bestEntryOuterStep (q : LevelArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let rowArgs : BestEntryRowArgs :=
    ⟨env.n, u, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let _ ← fillBestEntryRowProg rowArgs
  let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  Memory.write (frameBEntryBase env.ws env.n env.k + u) best
  pure (u + 1)

private abbrev BestEntryOuterStepSafe (w : ℕ) (q : LevelArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  let rowArgs : BestEntryRowArgs :=
    ⟨env.n, u, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
  u < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe bestEntryRowStep BestEntryRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem bestEntryOuterStep_realizes :
    Realizes .exact bestEntryOuterStep (appendWords encLevelArgs wordWords) wordWords
      BestEntryOuterStepSafe (fun _ _ => 0) := by
  unfold bestEntryOuterStep
  realize [fillBestEntryRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hu, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameMaskBase, frameBEntryBase, frameBase, curAdjBase, curCostBase,
          candPredBase, candCostBase]
        nlinarith)

private def bestEntryProg (a : LevelArgs) : Memory.Prog ℕ :=
  iterate bestEntryOuterStep a a.n 0

private theorem bestEntryProg_realizes :
    Realizes .exact bestEntryProg encLevelArgs wordWords
      (fun w a s => iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold bestEntryProg
  realize [bestEntryOuterStep_realizes]
  exact h

private structure BestExitRowArgs where
  n : ℕ
  col : ℕ
  adjBase : ℕ
  costBase : ℕ
  maskBase : ℕ
  parentBase : ℕ
  predOut : ℕ
  costOut : ℕ

private word_enc_structure encBestExitRowArgs : BestExitRowArgs where
  n : wordWords, col : wordWords, adjBase : wordWords, costBase : wordWords,
  maskBase : wordWords, parentBase : wordWords, predOut : wordWords, costOut : wordWords

private instance : WordEncoding BestExitRowArgs := ⟨8, encBestExitRowArgs⟩

private def bestExitRowStep (q : BestExitRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let x := Prod.snd q
  let inX ← Memory.read (env.maskBase + x)
  let axw ← Memory.read (env.adjBase + x * env.n + env.col)
  let cxw ← Memory.read (env.costBase + x * env.n + env.col)
  let fx ← Memory.read (env.parentBase + x)
  if inX = 1 ∧ axw = 1 then
    let cxfx ← Memory.read (env.costBase + x * env.n + fx)
    let diff ← signedSubProg (cxw, cxfx)
    Memory.write (env.predOut + x) 1
    Memory.write (env.costOut + x) diff
    pure (x + 1)
  else
    Memory.write (env.predOut + x) 0
    Memory.write (env.costOut + x) 0
    pure (x + 1)

private abbrev BestExitRowStepSafe (w : ℕ) (q : BestExitRowArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let x := Prod.snd q
  let cxw := s.mem (env.costBase + x * env.n + env.col)
  let fx := s.mem (env.parentBase + x)
  let cxfx := s.mem (env.costBase + x * env.n + fx)
  Fits w 2 ∧ Fits w (env.maskBase + x) ∧ Fits w (env.adjBase + x * env.n + env.col) ∧
    Fits w (env.costBase + x * env.n + env.col) ∧ Fits w (env.parentBase + x) ∧
    Fits w (env.predOut + x) ∧ Fits w (env.costOut + x) ∧ Fits w (x + 1) ∧
    (s.mem (env.maskBase + x) = 1 →
      Fits w (env.costBase + x * env.n + fx) ∧ Fits w (cxfx + 1) ∧
        Fits w (2 * (cxw / 2 + cxfx / 2) + 1))

private theorem bestExitRowStep_realizes :
    Realizes .exact bestExitRowStep (appendWords encBestExitRowArgs wordWords) wordWords
      BestExitRowStepSafe (fun _ _ => 0) := by
  unfold bestExitRowStep
  realize [signedSubProg_realizes]
  all_goals
    obtain ⟨h2, hm, ha, hc, hp, hpo, hco, hx, hsub⟩ := h
    first
    | exact h2
    | exact h2.of_le (by omega)
    | exact hm
    | exact ha
    | exact hc
    | exact hp
    | exact hpo
    | exact hco
    | exact hx
    | exact (hsub ‹_›).1
    | exact (hsub ‹_›).2.1
    | exact (hsub ‹_›).2.2

private def fillBestExitRowProg (a : BestExitRowArgs) : Memory.Prog ℕ :=
  iterate bestExitRowStep a a.n 0

private theorem fillBestExitRowProg_realizes :
    Realizes .exact fillBestExitRowProg encBestExitRowArgs wordWords
      (fun w a s => iterationSafe bestExitRowStep BestExitRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillBestExitRowProg
  realize [bestExitRowStep_realizes]
  exact h

private def bestExitOuterStep (q : LevelArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let col := Prod.snd q
  let _ ← Memory.read 0
  let rowArgs : BestExitRowArgs :=
    ⟨env.n, col, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, frameParentBase env.ws env.n env.k,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let _ ← fillBestExitRowProg rowArgs
  let best ← argMinArrayProg ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  Memory.write (frameBExitBase env.ws env.n env.k + col) best
  pure (col + 1)

private abbrev BestExitOuterStepSafe (w : ℕ) (q : LevelArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  let rowArgs : BestExitRowArgs :=
    ⟨env.n, col, curAdjBase env.ws env.n, curCostBase env.ws env.n,
      frameMaskBase env.ws env.n env.k, frameParentBase env.ws env.n env.k,
      candPredBase env.ws env.n, candCostBase env.ws env.n⟩
  let s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
  col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    iterationSafe bestExitRowStep BestExitRowStepSafe w rowArgs env.n 0 s ∧
    iterationSafe argMinStep ArgMinStepSafe w
      ⟨env.n, candPredBase env.ws env.n, candCostBase env.ws env.n⟩ env.n ⟨0, env.n, 0⟩ s1

private theorem bestExitOuterStep_realizes :
    Realizes .exact bestExitOuterStep (appendWords encLevelArgs wordWords) wordWords
      BestExitOuterStepSafe (fun _ _ => 0) := by
  unfold bestExitOuterStep
  realize [fillBestExitRowProg_realizes, argMinArrayProg_realizes]
  all_goals
    obtain ⟨hcol, hk, hws, hrow, harg⟩ := h
    first
    | exact hrow
    | exact harg
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBExitBase, frameBase, curAdjBase,
          curCostBase, candPredBase, candCostBase]
        nlinarith)

private def bestExitProg (a : LevelArgs) : Memory.Prog ℕ :=
  iterate bestExitOuterStep a a.n 0

private theorem bestExitProg_realizes :
    Realizes .exact bestExitProg encLevelArgs wordWords
      (fun w a s => iterationSafe bestExitOuterStep BestExitOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold bestExitProg
  realize [bestExitOuterStep_realizes]
  exact h

-- 8. `contractTablesProg`

private structure ContractRowArgs where
  n : ℕ
  r : ℕ
  x0 : ℕ
  u : ℕ
  ws : ℕ
  k : ℕ

private word_enc_structure encContractRowArgs : ContractRowArgs where
  n : wordWords, r : wordWords, x0 : wordWords, u : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ContractRowArgs := ⟨6, encContractRowArgs⟩

private abbrev unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding

private def contractAdjCellProg (q : ContractRowArgs × ℕ) : Memory.Prog Unit := do
  let env := Prod.fst q
  let col := Prod.snd q
  let inU ← Memory.read (frameMaskBase env.ws env.n env.k + env.u)
  let inW ← Memory.read (frameMaskBase env.ws env.n env.k + col)
  let auw ← Memory.read (curAdjBase env.ws env.n + env.u * env.n + col)
  let beU ← Memory.read (frameBEntryBase env.ws env.n env.k + env.u)
  let bxW ← Memory.read (frameBExitBase env.ws env.n env.k + col)
  let newAdj :=
    if inU = 1 then
      if env.u = env.x0 then
        if inW = 0 ∧ bxW < env.n then 1 else 0
      else if col = env.r then 1 else 0
    else if inW = 1 then
      if col = env.x0 ∧ beU < env.n then 1 else 0
    else auw
  Memory.write (nextAdjBase env.ws env.n + env.u * env.n + col) newAdj

private abbrev ContractAdjCellSafe (w : ℕ) (q : ContractRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  env.u < env.n ∧ col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n

private theorem contractAdjCellProg_realizes :
    Realizes .exact contractAdjCellProg (appendWords encContractRowArgs wordWords) unitWords
      ContractAdjCellSafe (fun _ _ => 0) := by
  unfold contractAdjCellProg
  realize
  all_goals
    obtain ⟨hu, hcol, hk, hws⟩ := h
    exact hws.of_le (by
      dsimp only [wsSize, frameMaskBase, frameBEntryBase, frameBExitBase, frameBase,
        curAdjBase, nextAdjBase]
      nlinarith)

private def contractCostCellProg (q : ContractRowArgs × ℕ) : Memory.Prog Unit := do
  let env := Prod.fst q
  let col := Prod.snd q
  let inU ← Memory.read (frameMaskBase env.ws env.n env.k + env.u)
  let inW ← Memory.read (frameMaskBase env.ws env.n env.k + col)
  let auw ← Memory.read (curAdjBase env.ws env.n + env.u * env.n + col)
  let cuw ← Memory.read (curCostBase env.ws env.n + env.u * env.n + col)
  let beU ← Memory.read (frameBEntryBase env.ws env.n env.k + env.u)
  let bxW ← Memory.read (frameBExitBase env.ws env.n env.k + col)
  let newCost ←
    if inU = 1 then
      if env.u = env.x0 then
        if inW = 0 ∧ bxW < env.n then do
          let cxw ← Memory.read (curCostBase env.ws env.n + bxW * env.n + col)
          let fx ← Memory.read (frameParentBase env.ws env.n env.k + bxW)
          let cxfx ← Memory.read (curCostBase env.ws env.n + bxW * env.n + fx)
          signedSubProg (cxw, cxfx)
        else pure 0
      else pure 0
    else if inW = 1 then
      if col = env.x0 ∧ beU < env.n then
        Memory.read (curCostBase env.ws env.n + env.u * env.n + beU)
      else pure 0
    else if auw = 1 then pure cuw
    else pure 0
  Memory.write (nextCostBase env.ws env.n + env.u * env.n + col) newCost

private abbrev ContractRowStepSafe (w : ℕ) (q : ContractRowArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  let bxW := s.mem (frameBExitBase env.ws env.n env.k + col)
  let cxw := s.mem (curCostBase env.ws env.n + bxW * env.n + col)
  let fx := s.mem (frameParentBase env.ws env.n env.k + bxW)
  let cxfx := s.mem (curCostBase env.ws env.n + bxW * env.n + fx)
  env.u < env.n ∧ col < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n ∧
    (s.mem (frameMaskBase env.ws env.n env.k + env.u) = 1 →
      env.u = env.x0 → s.mem (frameMaskBase env.ws env.n env.k + col) = 0 → bxW < env.n →
      fx < env.n ∧ Fits w (cxfx + 1) ∧ Fits w (2 * (cxw / 2 + cxfx / 2) + 1))

private theorem contractCostCellProg_realizes :
    Realizes .exact contractCostCellProg (appendWords encContractRowArgs wordWords) unitWords
      ContractRowStepSafe (fun _ _ => 0) := by
  unfold contractCostCellProg
  realize [signedSubProg_realizes]
  all_goals
    obtain ⟨hu, hcol, hk, hws, hsub⟩ := h
    have hfr := frame_le_frames hk
    have huc := List.mul_add_lt_sq hu hcol
    first
    | exact (hsub ‹_› ‹_› ‹_› ‹_›).2.1
    | exact (hsub ‹_› ‹_› ‹_› ‹_›).2.2
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase]
        omega)
    | exact hws.of_le (by
        have hbx : s.mem (frameBExitBase d.1.ws d.1.n d.1.k + d.2) < d.1.n := ‹_›
        have hbx_c := List.mul_add_lt_sq hbx hcol
        have hfx : s.mem (frameParentBase d.1.ws d.1.n d.1.k +
            s.mem (frameBExitBase d.1.ws d.1.n d.1.k + d.2)) < d.1.n :=
          (hsub ‹_› ‹_› ‹_› hbx).1
        have hbx_f := List.mul_add_lt_sq hbx hfx
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase] at hbx hbx_c hfx hbx_f ⊢
        omega)
    | exact hws.of_le (by
        have hbe : s.mem (frameBEntryBase d.1.ws d.1.n d.1.k + d.1.u) < d.1.n := ‹_›
        have hu_be := List.mul_add_lt_sq hu hbe
        dsimp only [wsSize, frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase,
          frameBase, curAdjBase, curCostBase, nextCostBase] at hbe hu_be ⊢
        omega)

private def contractRowStep (q : ContractRowArgs × ℕ) : Memory.Prog ℕ := do
  contractCostCellProg q
  contractAdjCellProg q
  pure (Prod.snd q + 1)

private theorem contractRowStep_realizes :
    Realizes .exact contractRowStep (appendWords encContractRowArgs wordWords) wordWords
      ContractRowStepSafe (fun _ _ => 0) := by
  unfold contractRowStep
  realize [contractCostCellProg_realizes, contractAdjCellProg_realizes]
  all_goals
    obtain ⟨hu, hcol, hk, hws, hadd⟩ := h
    first
    | exact ⟨hu, hcol, hk, hws, hadd⟩
    | exact ⟨hu, hcol, hk, hws⟩
    | exact hws.of_le (by dsimp only [wsSize]; nlinarith)

private def fillContractRowProg (a : ContractRowArgs) : Memory.Prog ℕ :=
  iterate contractRowStep a a.n 0

private theorem fillContractRowProg_realizes :
    Realizes .exact fillContractRowProg encContractRowArgs wordWords
      (fun w a s => iterationSafe contractRowStep ContractRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillContractRowProg
  realize [contractRowStep_realizes]
  exact h

private structure ContractArgs where
  n : ℕ
  r : ℕ
  x0 : ℕ
  ws : ℕ
  k : ℕ

private word_enc_structure encContractArgs : ContractArgs where
  n : wordWords, r : wordWords, x0 : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ContractArgs := ⟨5, encContractArgs⟩

private def contractOuterStep (q : ContractArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillContractRowProg ⟨env.n, env.r, env.x0, u, env.ws, env.k⟩
  pure (u + 1)

private abbrev ContractOuterStepSafe (w : ℕ) (q : ContractArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  Fits w (u + 1) ∧
    iterationSafe contractRowStep ContractRowStepSafe w
      ⟨env.n, env.r, env.x0, u, env.ws, env.k⟩ env.n 0 s

private theorem contractOuterStep_realizes :
    Realizes .exact contractOuterStep (appendWords encContractArgs wordWords) wordWords
      ContractOuterStepSafe (fun _ _ => 0) := by
  unfold contractOuterStep
  realize [fillContractRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

private def contractLoopProg (a : ContractArgs) : Memory.Prog ℕ :=
  iterate contractOuterStep a a.n 0

private theorem contractLoopProg_realizes :
    Realizes .exact contractLoopProg encContractArgs wordWords
      (fun w a s => iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold contractLoopProg
  realize [contractOuterStep_realizes]
  exact h

private def contractTablesProg (a : ContractArgs) : Memory.Prog ℕ := do
  let _ ← contractLoopProg a
  copyWordsProg ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩

private theorem contractTablesProg_realizes :
    Realizes .exact contractTablesProg encContractArgs wordWords
      (fun w a s =>
        let s1 := (Memory.spec 0).clientState s (contractLoopProg a)
        let cp : CopyArgs := ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩
        WsFits w a.ws a.n ∧
          iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s ∧
          iterationSafe copyStep CopyStepSafe w cp (2 * (a.n * a.n)) 0 s1)
      (fun _ _ => 0) := by
  unfold contractTablesProg
  realize [contractLoopProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hws, hloop, hcp⟩ := h
    first
    | exact hloop
    | exact hcp
    | exact hws.of_le (by
        dsimp only [wsSize, curAdjBase, nextAdjBase]
        nlinarith)

-- 9. `expandLevelProg`

private structure ExpandRowArgs where
  n : ℕ
  x0 : ℕ
  qx0 : ℕ
  bx : ℕ
  ws : ℕ
  k : ℕ

private word_enc_structure encExpandRowArgs : ExpandRowArgs where
  n : wordWords, x0 : wordWords, qx0 : wordWords, bx : wordWords, ws : wordWords, k : wordWords

private instance : WordEncoding ExpandRowArgs := ⟨6, encExpandRowArgs⟩

private def expandRowStep (q : ExpandRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let v := Prod.snd q
  let inV ← Memory.read (frameMaskBase env.ws env.n env.k + v)
  let fv ← Memory.read (frameParentBase env.ws env.n env.k + v)
  let qv ← Memory.read (curParentBase env.ws env.n + v)
  let bev ← Memory.read (frameBEntryBase env.ws env.n env.k + v)
  let outV :=
    if inV = 1 then
      if env.bx < env.n then
        if v = env.bx then env.qx0 else fv
      else fv
    else if qv = env.x0 then
      if bev < env.n then bev else v
    else qv
  Memory.write (nextParentBase env.ws env.n + v) outV
  pure (v + 1)

private abbrev ExpandRowStepSafe (w : ℕ) (q : ExpandRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let v := Prod.snd q
  v < env.n ∧ env.k < env.n ∧ WsFits w env.ws env.n

private theorem expandRowStep_realizes :
    Realizes .exact expandRowStep (appendWords encExpandRowArgs wordWords) wordWords
      ExpandRowStepSafe (fun _ _ => 0) := by
  unfold expandRowStep
  realize
  all_goals
    obtain ⟨hv, hk, hws⟩ := h
    exact hws.of_le (by
      dsimp only [wsSize, frameMaskBase, frameParentBase, frameBEntryBase, frameBase,
        curParentBase, nextParentBase]
      nlinarith)

private def fillExpandRowProg (a : ExpandRowArgs) : Memory.Prog ℕ :=
  iterate expandRowStep a a.n 0

private theorem fillExpandRowProg_realizes :
    Realizes .exact fillExpandRowProg encExpandRowArgs wordWords
      (fun w a s => iterationSafe expandRowStep ExpandRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillExpandRowProg
  realize [expandRowStep_realizes]
  exact h

private def expandLevelProg (a : LevelArgs) : Memory.Prog ℕ := do
  let x0 ← Memory.read (frameRepAddr a.ws a.n a.k)
  let qx0 ← Memory.read (curParentBase a.ws a.n + x0)
  let bx ← Memory.read (frameBExitBase a.ws a.n a.k + qx0)
  let _ ← fillExpandRowProg ⟨a.n, x0, qx0, bx, a.ws, a.k⟩
  copyWordsProg ⟨nextParentBase a.ws a.n, curParentBase a.ws a.n, a.n⟩

private abbrev ExpandLevelSafe (w : ℕ) (a : LevelArgs) (s : Memory.State) : Prop :=
  let x0 := s.mem (frameRepAddr a.ws a.n a.k)
  let qx0 := s.mem (curParentBase a.ws a.n + x0)
  let bx := s.mem (frameBExitBase a.ws a.n a.k + qx0)
  let rArgs : ExpandRowArgs := ⟨a.n, x0, qx0, bx, a.ws, a.k⟩
  let s1 := (Memory.spec 0).clientState s (fillExpandRowProg rArgs)
  let cArgs : CopyArgs := ⟨nextParentBase a.ws a.n, curParentBase a.ws a.n, a.n⟩
  a.k < a.n ∧ WsFits w a.ws a.n ∧ x0 < a.n ∧ qx0 < a.n ∧
    iterationSafe expandRowStep ExpandRowStepSafe w rArgs a.n 0 s ∧
    iterationSafe copyStep CopyStepSafe w cArgs a.n 0 s1

private theorem expandLevelProg_realizes :
    Realizes .exact expandLevelProg encLevelArgs wordWords
      ExpandLevelSafe (fun _ _ => 0) := by
  unfold expandLevelProg
  realize [fillExpandRowProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hk, hws, hx0, hqx0, hexp, hcopy⟩ := h
    first
    | exact hexp
    | exact hcopy
    | exact hws.of_le (by
        dsimp only [wsSize, frameRepAddr, frameBExitBase, frameBase, curParentBase,
          nextParentBase] at hx0 hqx0 ⊢
        nlinarith)

-- 10. `edmondsCoreProg`: forward contraction pass + backward expansion pass

private structure CoreArgs where
  n : ℕ
  r : ℕ
  ws : ℕ

private word_enc_structure encCoreArgs : CoreArgs where
  n : wordWords, r : wordWords, ws : wordWords

private instance : WordEncoding CoreArgs := ⟨3, encCoreArgs⟩

private structure ForwardState where
  k : ℕ
  status : ℕ
  depth : ℕ

private word_enc_structure encForwardState : ForwardState where
  k : wordWords, status : wordWords, depth : wordWords

private instance : WordEncoding ForwardState := ⟨3, encForwardState⟩

private def contractRoundBodyProg (a : ContractArgs) : Memory.Prog ℕ := do
  Memory.write (frameRepAddr a.ws a.n a.k) a.x0
  let _ ← cycleMaskProg
    ⟨a.n, frameParentBase a.ws a.n a.k, frameMaskBase a.ws a.n a.k, a.x0⟩
  let _ ← bestEntryProg ⟨a.n, a.ws, a.k⟩
  let _ ← bestExitProg ⟨a.n, a.ws, a.k⟩
  contractTablesProg a

private abbrev ContractRoundBodySafe (w : ℕ) (a : ContractArgs) (s : Memory.State) : Prop :=
  let s0 : Memory.State := ⟨Function.update s.mem (frameRepAddr a.ws a.n a.k) a.x0, s.frontier⟩
  let cmArgs : CycleMaskArgs :=
    ⟨a.n, frameParentBase a.ws a.n a.k, frameMaskBase a.ws a.n a.k, a.x0⟩
  let s0z := (Memory.spec 0).clientState s0 (zeroWordsProg ⟨cmArgs.maskBase, cmArgs.n⟩)
  let s1 := (Memory.spec 0).clientState s0 (cycleMaskProg cmArgs)
  let lvArgs : LevelArgs := ⟨a.n, a.ws, a.k⟩
  let s2 := (Memory.spec 0).clientState s1 (bestEntryProg lvArgs)
  let s3 := (Memory.spec 0).clientState s2 (bestExitProg lvArgs)
  let s4 := (Memory.spec 0).clientState s3 (contractLoopProg a)
  let cp : CopyArgs := ⟨nextAdjBase a.ws a.n, curAdjBase a.ws a.n, 2 * (a.n * a.n)⟩
  a.k < a.n ∧ WsFits w a.ws a.n ∧
    iterationSafe zeroStep ZeroStepSafe w ⟨cmArgs.maskBase, cmArgs.n⟩ cmArgs.n 0 s0 ∧
    iterationSafe cycleMaskStep CycleMaskStepSafe w cmArgs cmArgs.n ⟨0, cmArgs.x0⟩ s0z ∧
    iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w lvArgs lvArgs.n 0 s1 ∧
    iterationSafe bestExitOuterStep BestExitOuterStepSafe w lvArgs lvArgs.n 0 s2 ∧
    iterationSafe contractOuterStep ContractOuterStepSafe w a a.n 0 s3 ∧
    iterationSafe copyStep CopyStepSafe w cp (2 * (a.n * a.n)) 0 s4

private theorem contractRoundBodyProg_realizes :
    Realizes .exact contractRoundBodyProg encContractArgs wordWords
      ContractRoundBodySafe (fun _ _ => 0) := by
  unfold contractRoundBodyProg
  realize [cycleMaskProg_realizes, bestEntryProg_realizes,
    bestExitProg_realizes, contractTablesProg_realizes]
  all_goals
    obtain ⟨hk, hws, hz, hcm, hbe, hbx, hct, hcp⟩ := h
    first
    | exact hz
    | exact hcm
    | exact hbe
    | exact hbx
    | exact hct
    | exact hcp
    | exact hws
    | exact hws.of_le (by
        dsimp only [wsSize, frameRepAddr, frameParentBase, frameMaskBase, frameBase]
        nlinarith)

private def forwardStep (q : CoreArgs × ForwardState) : Memory.Prog ForwardState := do
  let env := Prod.fst q
  let st := Prod.snd q
  let _ ← Memory.read 0
  if st.status = 0 then
    let feas ← selectParentsProg ⟨env.n, env.r, env.ws, st.k⟩
    if feas = 0 then
      pure ⟨st.k + 1, 2, st.depth⟩
    else
      let x0 ← findCycleProg ⟨env.n, env.r, frameParentBase env.ws env.n st.k⟩
      if x0 = env.n then
        let _ ← copyWordsProg ⟨frameParentBase env.ws env.n st.k, curParentBase env.ws env.n, env.n⟩
        pure ⟨st.k + 1, 1, st.k⟩
      else
        let _ ← contractRoundBodyProg ⟨env.n, env.r, x0, env.ws, st.k⟩
        pure ⟨st.k + 1, 0, st.k + 1⟩
  else
    pure ⟨st.k + 1, st.status, st.depth⟩

private abbrev ForwardStepSafe (w : ℕ) (q : CoreArgs × ForwardState) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let st := Prod.snd q
  let selArgs : SelectArgs := ⟨env.n, env.r, env.ws, st.k⟩
  let sSel := (Memory.spec 0).clientState s (selectParentsProg selArgs)
  let fcArgs : FindCycleArgs := ⟨env.n, env.r, frameParentBase env.ws env.n st.k⟩
  let x0 := (Memory.spec 0).clientResult sSel (findCycleProg fcArgs)
  let sFc := (Memory.spec 0).clientState sSel (findCycleProg fcArgs)
  let cpArgs : CopyArgs := ⟨frameParentBase env.ws env.n st.k, curParentBase env.ws env.n, env.n⟩
  st.k < env.n ∧ WsFits w env.ws env.n ∧
    (st.status = 0 →
      iterationSafe selectOuterStep SelectOuterStepSafe w selArgs env.n ⟨0, 1⟩ s ∧
      ((Memory.spec 0).clientResult s (selectParentsProg selArgs) ≠ 0 →
        iterationSafe findCycleOuterStep FindCycleOuterStepSafe w fcArgs env.n ⟨0, env.n⟩ sSel ∧
        (x0 = env.n → iterationSafe copyStep CopyStepSafe w cpArgs env.n 0 sFc) ∧
        (x0 ≠ env.n → ContractRoundBodySafe w ⟨env.n, env.r, x0, env.ws, st.k⟩ sFc)))

private theorem forwardStep_realizes :
    Realizes .exact forwardStep (appendWords encCoreArgs encForwardState) encForwardState
      ForwardStepSafe (fun _ _ => 0) := by
  unfold forwardStep
  realize [selectParentsProg_realizes, findCycleProg_realizes, copyWordsProg_realizes,
    contractRoundBodyProg_realizes]
  all_goals
    obtain ⟨hk, hws, hst0⟩ := h
    first
    | exact (hst0 ‹_›).1
    | exact ((hst0 ‹_›).2 ‹_›).1
    | exact ((hst0 ‹_›).2 ‹_›).2.1 ‹_›
    | exact ((hst0 ‹_›).2 ‹_›).2.2 ‹_›
    | exact hws.of_le (by
        dsimp only [wsSize, frameParentBase, frameBase, curParentBase]
        nlinarith)

private def forwardProg (a : CoreArgs) : Memory.Prog ForwardState :=
  iterate forwardStep a a.n ⟨0, 0, 0⟩

private theorem forwardProg_realizes :
    Realizes .exact forwardProg encCoreArgs encForwardState
      (fun w a s => iterationSafe forwardStep ForwardStepSafe w a a.n ⟨0, 0, 0⟩ s)
      (fun _ _ => 0) := by
  unfold forwardProg
  realize [forwardStep_realizes]
  exact h

private structure BackwardArgs where
  n : ℕ
  ws : ℕ
  depth : ℕ

private word_enc_structure encBackwardArgs : BackwardArgs where
  n : wordWords, ws : wordWords, depth : wordWords

private instance : WordEncoding BackwardArgs := ⟨3, encBackwardArgs⟩

private def backwardStep (q : BackwardArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let j := Prod.snd q
  let _ ← Memory.read 0
  let k := env.depth - (j + 1)
  let _ ← expandLevelProg ⟨env.n, env.ws, k⟩
  pure (j + 1)

private abbrev BackwardStepSafe (w : ℕ) (q : BackwardArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let j := Prod.snd q
  let k := env.depth - (j + 1)
  j + 1 ≤ env.depth ∧ Fits w (j + 1) ∧ ExpandLevelSafe w ⟨env.n, env.ws, k⟩ s

private theorem backwardStep_realizes :
    Realizes .exact backwardStep (appendWords encBackwardArgs wordWords) wordWords
      BackwardStepSafe (fun _ _ => 0) := by
  unfold backwardStep
  realize [expandLevelProg_realizes]
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def backwardProg (a : BackwardArgs) : Memory.Prog ℕ :=
  iterate backwardStep a a.depth 0

private theorem backwardProg_realizes :
    Realizes .exact backwardProg encBackwardArgs wordWords
      (fun w a s => iterationSafe backwardStep BackwardStepSafe w a a.depth 0 s)
      (fun _ _ => 0) := by
  unfold backwardProg
  realize [backwardStep_realizes]
  exact h

private def edmondsCoreProg (a : CoreArgs) : Memory.Prog ℕ := do
  let res ← forwardProg a
  if res.status = 1 then
    let _ ← backwardProg ⟨a.n, a.ws, res.depth⟩
    pure 1
  else
    pure 0

private theorem edmondsCoreProg_realizes :
    Realizes .exact edmondsCoreProg encCoreArgs wordWords
      (fun w a s =>
        let res := (Memory.spec 0).clientResult s (forwardProg a)
        let s1 := (Memory.spec 0).clientState s (forwardProg a)
        Fits w 1 ∧
          iterationSafe forwardStep ForwardStepSafe w a a.n ⟨0, 0, 0⟩ s ∧
          (res.status = 1 →
            iterationSafe backwardStep BackwardStepSafe w ⟨a.n, a.ws, res.depth⟩ res.depth 0 s1))
      (fun _ _ => 0) := by
  unfold edmondsCoreProg
  realize [forwardProg_realizes, backwardProg_realizes]
  all_goals
    obtain ⟨h1, hfwd, hbwd⟩ := h
    first | exact h1 | exact hfwd | exact hbwd ‹_›

/-! ### Correctness, admissibility, and `O(n³)` memory-cost specifications -/

private theorem foldl_take_finRange_succ {α : Type*} {n k : ℕ} (hk : k < n)
    (g : α → Fin n → α) (init : α) :
    ((List.finRange n).take (k + 1)).foldl g init =
      g (((List.finRange n).take k).foldl g init) ⟨k, hk⟩ := by
  rw [List.take_succ_finRange hk, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem foldl_range_succ {α : Type*} (m : ℕ) (g : α → ℕ → α) (init : α) :
    (List.range (m + 1)).foldl g init = g ((List.range m).foldl g init) m := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem copyWordsProg_spec {w : ℕ} (a : CopyArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.len ≤ s₀.frontier) (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hdisj : a.src + a.len ≤ a.dst ∨ a.dst + a.len ≤ a.src)
    (hfit_src : Fits w (a.src + a.len)) (hfit_dst : Fits w (a.dst + a.len))
    (hfit_len : Fits w a.len) (hval : ∀ i < a.len, Fits w (s₀.mem (a.src + i))) :
    let s' := (Memory.spec 0).clientState s₀ (copyWordsProg a)
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (copyWordsProg a)) ∧
      memoryCost (copyWordsProg a) s₀ ≤ 2 * a.len ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬(a.dst ≤ x ∧ x < a.dst + a.len) → s'.mem x = s₀.mem x) ∧
      (∀ i < a.len, s'.mem (a.dst + i) = s₀.mem (a.src + i)) := by
  have h := iterate_spec copyStep CopyStepSafe w a 2 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ j < k, s.mem (a.dst + j) = s₀.mem (a.src + j)) ∧
      (∀ j < a.len, s.mem (a.src + j) = s₀.mem (a.src + j)))
    (fun x => a.dst ≤ x ∧ x < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hdst, hsrc⟩ => by
      subst idx
      have hsrc_eq := hsrc k hk
      refine ⟨by dsimp only [CopyStepSafe]; exact ⟨hfit_src.of_le (by omega),
          hfit_dst.of_le (by omega), hfit_len.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold copyStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_write_bind (by omega) (hsrc_eq ▸ hval k hk) (validHistory_pure w _ _))
      · unfold copyStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [copyStep, client_simps]
      · intro x hx
        simp only [copyStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp [copyStep, client_simps]
      · simpa [copyStep, client_simps] using hfr
      · intro j hj
        simp only [copyStep, client_simps]
        by_cases hjk : j = k
        · subst j
          simp [hsrc_eq]
        · rw [Function.update_of_ne (by omega)]
          exact hdst j (by omega)
      · intro j hj
        simp only [copyStep, client_simps]
        rw [Function.update_of_ne (by omega)]
        exact hsrc j hj)
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  unfold copyWordsProg
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private theorem zeroWordsProg_spec {w : ℕ} (a : ZeroArgs) (s₀ : Memory.State)
    (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hfit_dst : Fits w (a.dst + a.len)) (hfit_len : Fits w a.len) :
    let s' := (Memory.spec 0).clientState s₀ (zeroWordsProg a)
    iterationSafe zeroStep ZeroStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (zeroWordsProg a)) ∧
      memoryCost (zeroWordsProg a) s₀ ≤ a.len ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬(a.dst ≤ x ∧ x < a.dst + a.len) → s'.mem x = s₀.mem x) ∧
      (∀ i < a.len, s'.mem (a.dst + i) = 0) := by
  have h := iterate_spec zeroStep ZeroStepSafe w a 1 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧ ∀ j < k, s.mem (a.dst + j) = 0)
    (fun x => a.dst ≤ x ∧ x < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hz⟩ => by
      subst idx
      refine ⟨by dsimp only [ZeroStepSafe]; exact ⟨hfit_dst.of_le (by omega),
          hfit_len.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold zeroStep
        dsimp only
        exact validHistory_write_bind
          (by rw [hfr]; omega) (fits_zero w) (validHistory_pure w _ _)
      · unfold zeroStep
        dsimp only
        rw [memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [zeroStep, client_simps]
      · intro x hx
        simp only [zeroStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp [zeroStep, client_simps]
      · simpa [zeroStep, client_simps] using hfr
      · intro j hj
        simp only [zeroStep, client_simps]
        by_cases hjk : j = k
        · subst j
          simp
        · rw [Function.update_of_ne (by omega)]
          exact hz j (by omega))
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  unfold zeroWordsProg
  refine ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private def optFinIdx {n : ℕ} : Option (Fin n) → ℕ
  | some j => j.1
  | none => n

private theorem argMinArrayProg_spec {w n : ℕ} (predBase costBase : ℕ)
    (pred : Fin n → Bool) (val : Fin n → ℤ) (s₀ : Memory.State)
    (h2 : Fits w 2) (hfit_p : Fits w (predBase + n)) (hfit_c : Fits w (costBase + n))
    (hfit_n : Fits w n)
    (hp_f : predBase + n ≤ s₀.frontier) (hc_f : costBase + n ≤ s₀.frontier)
    (hp_mem : ∀ i : Fin n, s₀.mem (predBase + i.1) = if pred i then 1 else 0)
    (hc_mem : ∀ i : Fin n, s₀.mem (costBase + i.1) = Signed.encode (val i)) :
    let a : ArgMinArgs := ⟨n, predBase, costBase⟩
    iterationSafe argMinStep ArgMinStepSafe w a n ⟨0, n, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (argMinArrayProg a)) ∧
      memoryCost (argMinArrayProg a) s₀ ≤ 2 * n ∧
      (Memory.spec 0).clientState s₀ (argMinArrayProg a) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (argMinArrayProg a) = optFinIdx (argMinFin n pred val) := by
  let a : ArgMinArgs := ⟨n, predBase, costBase⟩
  let stepFn := fun (acc : Option (Fin n)) (i : Fin n) =>
    if pred i then List.argAux (fun x y => val x < val y) acc i else acc
  have h := iterate_spec argMinStep ArgMinStepSafe w a 2 n
    (fun k st s =>
      let acc := ((List.finRange n).take k).foldl stepFn none
      st.idx = k ∧ s = s₀ ∧ st.bestIdx = optFinIdx acc ∧
        ∀ j, acc = some j → st.bestCost = Signed.encode (val j))
    (fun _ => False)
    (fun k hk st s ⟨hidx, hs, hbi, hbc⟩ => by
      rcases st with ⟨idx, bestIdx, bestCost⟩
      dsimp only at hidx hbi hbc
      subst idx s
      have hp_k : s₀.mem (predBase + k) = if pred ⟨k, hk⟩ then 1 else 0 := hp_mem ⟨k, hk⟩
      have hc_k : s₀.mem (costBase + k) = Signed.encode (val ⟨k, hk⟩) := hc_mem ⟨k, hk⟩
      refine ⟨by dsimp only [ArgMinStepSafe, a]; exact ⟨h2, hfit_p.of_le (by omega),
          hfit_c.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, fun _ _ => ?_, ?_⟩
      · unfold argMinStep
        exact validHistory_read_bind (by dsimp only [a]; omega)
          (validHistory_read_bind (by dsimp only [a]; omega)
            (by dsimp only; split_ifs <;> trivial))
      · unfold argMinStep
        dsimp only [a]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        split_ifs <;> simp [client_simps]
      · unfold argMinStep
        dsimp only [a]
        simp [client_simps]
      · unfold argMinStep
        dsimp only [a]
        simp [client_simps]
      · rw [foldl_take_finRange_succ hk stepFn none]
        generalize hacc : ((List.finRange n).take k).foldl stepFn none = acc at hbi hbc ⊢
        dsimp only [stepFn]
        unfold argMinStep
        dsimp only [a]
        simp only [client_simps, hp_k, hc_k]
        cases hp_bool : pred ⟨k, hk⟩
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one, client_simps]
          exact ⟨trivial, trivial, hbi, hbc⟩
        · simp only [↓reduceIte]
          cases acc with
          | none =>
            have hbin : bestIdx = n := hbi.trans (by simp [optFinIdx])
            simp [hbin, List.argAux, optFinIdx, client_simps]
          | some j =>
            have hbin : bestIdx = j.1 := hbi.trans (by simp [optFinIdx])
            have hbne : bestIdx ≠ n := by omega
            have hbcj : bestCost = Signed.encode (val j) := hbc j rfl
            simp only [hbne, ↓reduceIte, hbcj, List.argAux]
            by_cases hlt : val ⟨k, hk⟩ < val j
            · have hw : SignedLtWord (Signed.encode (val ⟨k, hk⟩)) (Signed.encode (val j)) :=
                (signedLtWord_iff _ _).mpr hlt
              simp only [hlt, hw, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, trivial, fun j' hj' => by cases hj'; rfl⟩
            · have hnw : ¬SignedLtWord (Signed.encode (val ⟨k, hk⟩)) (Signed.encode (val j)) :=
                mt (signedLtWord_iff _ _).mp hlt
              simp only [hlt, hnw, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, hbin, fun j' hj' => by cases hj'; rfl⟩)
    ⟨0, n, 0⟩ s₀ ⟨rfl, rfl, rfl, fun _ h => by simp at h⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe, hvh, hmc, _, _, _, hs_eq, hbi_n, _⟩ := h
  unfold argMinArrayProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp only [client_simps]; exact hs_eq,
    ?_⟩
  simp only [client_simps]
  exact hbi_n.trans (by simp [argMinFin, stepFn, htake])

private theorem fillSelectRowProg_spec {w n ws : ℕ} (vFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (s : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1])) :
    let rowArgs : SelectRowArgs :=
      ⟨n, vFin.1, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
    let s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
    iterationSafe selectRowStep SelectRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillSelectRowProg rowArgs)) ∧
      memoryCost (fillSelectRowProg rowArgs) s ≤ 4 * n ∧
      s1.frontier = s.frontier ∧
      (∀ x, ¬(candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) → s1.mem x = s.mem x) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.1 * n + col.1) =
        if a[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.1 * n + col.1) =
        Signed.encode c[u.1][col.1]) ∧
      (∀ col : Fin n,
        s1.mem (candPredBase ws n + col.1) = (if a[vFin.1][col.1] && col != vFin then 1 else 0) ∧
        s1.mem (candCostBase ws n + col.1) = Signed.encode c[vFin.1][col.1]) := by
  let rowArgs : SelectRowArgs :=
    ⟨n, vFin.1, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hv_lt := vFin.isLt
  have hrow := iterate_spec selectRowStep SelectRowStepSafe w rowArgs 4 n
    (fun col idx sr => idx = col ∧ sr.frontier = s.frontier ∧
      (∀ u c0 : Fin n, sr.mem (curAdjBase ws n + u.1 * n + c0.1) =
        if a[u.1][c0.1] then 1 else 0) ∧
      (∀ u c0 : Fin n, sr.mem (curCostBase ws n + u.1 * n + c0.1) =
        Signed.encode c[u.1][c0.1]) ∧
      (∀ c0 : Fin n, c0.1 < col →
        sr.mem (candPredBase ws n + c0.1) =
          (if a[vFin.1][c0.1] && c0 != vFin then 1 else 0) ∧
        sr.mem (candCostBase ws n + c0.1) = Signed.encode c[vFin.1][c0.1]))
    (fun x => candPredBase ws n ≤ x ∧ x < candCostBase ws n + n)
    (fun col hcol idx sr ⟨hidx_c, hfr_r, ha_r, hc_r, hdone⟩ => by
      subst idx
      have ha_mc : sr.mem (curAdjBase ws n + vFin.1 * n + col) =
          if a[vFin.1][col] then 1 else 0 := ha_r vFin ⟨col, hcol⟩
      have hc_mc : sr.mem (curCostBase ws n + vFin.1 * n + col) =
          Signed.encode c[vFin.1][col] := hc_r vFin ⟨col, hcol⟩
      refine ⟨by dsimp only [SelectRowStepSafe, rowArgs]; exact ⟨h1,
          hws.of_le (by dsimp only [wsSize, curAdjBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, curCostBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize]; nlinarith)⟩, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · unfold selectRowStep
        dsimp only [rowArgs]
        exact validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; nlinarith)
            (validHistory_write_bind
              (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; nlinarith)
              (by split_ifs <;> first | exact h1 | exact fits_zero w)
              (validHistory_write_bind
                (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; nlinarith)
                (hc_mc ▸ hfit_c vFin ⟨col, hcol⟩)
                (validHistory_pure w _ _))))
      · unfold selectRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [selectRowStep, rowArgs, client_simps]
      · intro x hx
        dsimp only [candPredBase, candCostBase] at hx
        simp only [selectRowStep, rowArgs, client_simps, candPredBase, candCostBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp [selectRowStep, rowArgs, client_simps]
      · simpa [selectRowStep, rowArgs, client_simps] using hfr_r
      · intro u c0
        have := u.isLt; have := c0.isLt
        simp only [selectRowStep, rowArgs, client_simps]
        rw [Function.update_of_ne (by dsimp only [curAdjBase, candCostBase]; nlinarith),
          Function.update_of_ne (by dsimp only [curAdjBase, candPredBase]; nlinarith)]
        exact ha_r u c0
      · intro u c0
        have := u.isLt; have := c0.isLt
        simp only [selectRowStep, rowArgs, client_simps]
        rw [Function.update_of_ne (by dsimp only [curCostBase, candCostBase]; nlinarith),
          Function.update_of_ne (by dsimp only [curCostBase, candPredBase]; nlinarith)]
        exact hc_r u c0
      · intro c0 hc0
        simp only [selectRowStep, rowArgs, client_simps]
        by_cases heq : c0.1 = col
        · have hc0_eq : c0 = ⟨col, hcol⟩ := Fin.ext heq
          subst hc0_eq
          simp only [Function.update_self]
          rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_self]
          simp only [ha_mc, hc_mc]
          refine ⟨?_, trivial⟩
          by_cases hab : a[vFin.1][col] = true <;> by_cases hne : col = vFin.1 <;>
            simp [hab, hne, bne_iff_ne, Fin.ext_iff]
        · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
          exact hdone c0 (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  unfold fillSelectRowProg
  exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.1,
    hrow.2.2.2.2.2.2.2.1, hrow.2.2.2.2.2.2.2.2.1,
    fun col => hrow.2.2.2.2.2.2.2.2.2 col col.isLt⟩

private theorem selectParentsProg_spec {w n ws k : ℕ} (r : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1])) :
    let sa : SelectArgs := ⟨n, r.1, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (selectParentsProg sa)
    let sel := selectParents a c r
    (Fits w 1 ∧ iterationSafe selectOuterStep SelectOuterStepSafe w sa n ⟨0, 1⟩ s₀) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (selectParentsProg sa)) ∧
      memoryCost (selectParentsProg sa) s₀ ≤ (6 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬((candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) ∨
          (frameParentBase ws n k ≤ x ∧ x < frameParentBase ws n k + n)) →
        s'.mem x = s₀.mem x) ∧
      (Memory.spec 0).clientResult s₀ (selectParentsProg sa) = (if sel.feasible then 1 else 0) ∧
      (∀ v : Fin n, s'.mem (frameParentBase ws n k + v.1) = (sel.parents[v.1]).1) := by
  let sa : SelectArgs := ⟨n, r.1, ws, k⟩
  let optFn : Fin n → Option (Fin n) := fun v =>
    if v = r then some r
    else argMinFin n (fun col => a[v.1][col.1] && col != v) (fun col => c[v.1][col.1])
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hn_pos : 0 < n := r.pos
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec selectOuterStep SelectOuterStepSafe w sa (6 * n + 2) n
    (fun m st s =>
      let feasM := ((List.finRange n).take m).foldl (fun acc v => acc && (optFn v).isSome) true
      st.v = m ∧ st.feas = (if feasM then 1 else 0) ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
          if a[u.1][col.1] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
          Signed.encode c[u.1][col.1]) ∧
        (∀ j : Fin n, j.1 < m →
          s.mem (frameParentBase ws n k + j.1) = ((optFn j).getD j).1))
    (fun x => (candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) ∨
      (frameParentBase ws n k ≤ x ∧ x < frameParentBase ws n k + n))
    (fun m hm st s ⟨hv, hfeas, hfr, ha_s, hc_s, hpar⟩ => by
      rcases st with ⟨vIdx, feasBit⟩
      dsimp only at hv hfeas
      subst vIdx
      set vFin : Fin n := ⟨m, hm⟩
      let rowArgs : SelectRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
      have hrow := fillSelectRowProg_spec vFin a c s hws (by rw [hfr]; exact hf) ha_s hc_s hfit_c
      set s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun col => a[m][col.1] && col != vFin) (fun col => c[m][col.1]) s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun col => (hrow.2.2.2.2.2.2.2 col).1)
        (fun col => (hrow.2.2.2.2.2.2.2 col).2)
      refine ⟨by dsimp only [SelectOuterStepSafe, sa]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold selectOuterStep
        dsimp only [sa]
        refine validHistory_read_bind (by omega) ?_
        by_cases hmr : m = r.1
        · simp only [hmr, ↓reduceIte]
          exact validHistory_write_bind
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr ⊢; nlinarith)
            (hws.of_le (by dsimp only [wsSize]; omega))
            (validHistory_pure w _ _)
        · simp only [hmr, ↓reduceIte]
          refine validHistory_bind_step hrow.2.1 ?_
          refine validHistory_bind_step harg.2.1 ?_
          rw [harg.2.2.2.1]
          split_ifs
          · exact validHistory_write_bind
              (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr ⊢;
                  rw [hrow.2.2.2.1]; nlinarith)
              (hws.of_le (by dsimp only [wsSize]; omega))
              (validHistory_pure w _ _)
          · exact validHistory_write_bind
              (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr ⊢;
                  rw [hrow.2.2.2.1]; nlinarith)
              (hws.of_le (by dsimp only [wsSize]; omega))
              (validHistory_pure w _ _)
      · unfold selectOuterStep
        dsimp only [sa]
        rw [memoryCost_bind', memoryCost_read, clientState_read]
        by_cases hmr : m = r.1
        · simp only [hmr, ↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
          omega
        · simp only [hmr, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_bind', harg.2.2.2.1]
          have hc_row : memoryCost (fillSelectRowProg rowArgs) s ≤ 4 * n := hrow.2.2.1
          have hc_arg :
              memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
                2 * n := harg.2.2.1
          dsimp only [rowArgs, s1] at hc_row hc_arg ⊢
          split_ifs <;>
            simp only [memoryCost_bind', memoryCost_write, client_simps] <;> omega
      · unfold selectOuterStep
        dsimp only [sa]
        by_cases hmr : m = r.1
        · simp [hmr, client_simps, hfr]
        · have harg_s := harg.2.2.2.1
          have hrow_fr := hrow.2.2.2.1
          dsimp only [s1, rowArgs, vFin] at harg_s hrow_fr
          simp [hmr, client_simps, harg_s, hrow_fr, hfr]
      · intro x hx
        unfold selectOuterStep
        dsimp only [sa]
        have hx_p : x ≠ frameParentBase ws n k + m := by
          intro heq
          exact hx (Or.inr ⟨by omega, by omega⟩)
        by_cases hmr : m = r.1
        · simp only [hmr, ↓reduceIte, client_simps]
          rw [hmr] at hx_p
          exact Function.update_of_ne hx_p _ _
        · have harg_s := harg.2.2.2.1
          dsimp only [s1, rowArgs] at harg_s
          have hs1_x : ((Memory.spec 0).clientState s (fillSelectRowProg rowArgs)).mem x =
              s.mem x := hrow.2.2.2.2.1 x (fun hcand => hx (Or.inl hcand))
          dsimp only [rowArgs] at hs1_x
          simp [hmr, client_simps, harg_s, Function.update_of_ne hx_p, hs1_x]
      · rw [foldl_take_finRange_succ hm]
        unfold selectOuterStep
        dsimp only [sa]
        by_cases hmr : m = r.1
        · have hopt_r : optFn r = some r := by simp [optFn]
          simp only [hmr, ↓reduceIte, client_simps]
          refine ⟨trivial, ?_, hfr, ?_, ?_, ?_⟩
          · rw [show (⟨r.1, _⟩ : Fin n) = r from Fin.ext rfl, hopt_r]
            simp [hfeas, hmr]
          · intro u col
            have := List.mul_add_lt_sq u.isLt col.isLt
            rw [Function.update_of_ne
              (by dsimp only [curAdjBase, frameParentBase, frameBase]; omega)]
            exact ha_s u col
          · intro u col
            have := List.mul_add_lt_sq u.isLt col.isLt
            rw [Function.update_of_ne
              (by dsimp only [curCostBase, frameParentBase, frameBase]; omega)]
            exact hc_s u col
          · intro j hj
            by_cases hjm : j.1 = m
            · have hjr : j = r := Fin.ext (hjm.trans hmr)
              subst hjr
              simp [hopt_r]
            · rw [Function.update_of_ne (by omega)]
              exact hpar j (by omega)
        · have hvr : vFin ≠ r := fun h => hmr (congrArg Fin.val h)
          have hopt_v : optFn vFin =
              argMinFin n (fun col => a[m][col.1] && col != vFin) (fun col => c[m][col.1]) := by
            simp [optFn, hvr, vFin]
          have harg_s := harg.2.2.2.1
          have harg_r := harg.2.2.2.2
          dsimp only [s1, rowArgs, vFin] at harg_s harg_r
          simp only [hmr, ↓reduceIte, client_simps, harg_s, harg_r]
          rw [show (⟨m, hm⟩ : Fin n) = vFin from rfl, ← hopt_v]
          have hrow_fr := hrow.2.2.2.1
          have hrow_mod := hrow.2.2.2.2.1
          have hrow_a := hrow.2.2.2.2.2.1
          have hrow_c := hrow.2.2.2.2.2.2.1
          dsimp only [rowArgs, vFin] at hrow_fr hrow_mod hrow_a hrow_c
          cases hopt_case : optFn vFin with
          | some wBest =>
            have hwlt : wBest.1 < n := wBest.isLt
            simp only [optFinIdx, hwlt, ↓reduceIte, client_simps, Option.isSome_some,
              Bool.and_true]
            refine ⟨trivial, hfeas, hrow_fr.trans hfr, ?_, ?_, ?_⟩
            · intro u col
              have := List.mul_add_lt_sq u.isLt col.isLt
              rw [Function.update_of_ne
                (by dsimp only [curAdjBase, frameParentBase, frameBase]; omega)]
              exact hrow_a u col
            · intro u col
              have := List.mul_add_lt_sq u.isLt col.isLt
              rw [Function.update_of_ne
                (by dsimp only [curCostBase, frameParentBase, frameBase]; omega)]
              exact hrow_c u col
            · intro j hj
              by_cases hjm : j.1 = m
              · have hjv : j = vFin := Fin.ext hjm
                subst hjv
                simp [hopt_case, vFin]
              · rw [Function.update_of_ne (by omega),
                  hrow_mod _ (by
                    dsimp only [candPredBase, candCostBase, frameParentBase, frameBase]; omega)]
                exact hpar j (by omega)
          | none =>
            simp only [optFinIdx, lt_irrefl, ↓reduceIte, client_simps, Option.isSome_none,
              Bool.and_false]
            refine ⟨trivial, rfl, hrow_fr.trans hfr, ?_, ?_, ?_⟩
            · intro u col
              have := List.mul_add_lt_sq u.isLt col.isLt
              rw [Function.update_of_ne
                (by dsimp only [curAdjBase, frameParentBase, frameBase]; omega)]
              exact hrow_a u col
            · intro u col
              have := List.mul_add_lt_sq u.isLt col.isLt
              rw [Function.update_of_ne
                (by dsimp only [curCostBase, frameParentBase, frameBase]; omega)]
              exact hrow_c u col
            · intro j hj
              by_cases hjm : j.1 = m
              · have hjv : j = vFin := Fin.ext hjm
                subst hjv
                simp [hopt_case, vFin]
              · rw [Function.update_of_ne (by omega),
                  hrow_mod _ (by
                    dsimp only [candPredBase, candCostBase, frameParentBase, frameBase]; omega)]
                exact hpar j (by omega))
    ⟨0, 1⟩ s₀ ⟨rfl, rfl, rfl, ha, hc, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe_it, hvh_it, hmc_it, hfr_it, hmod_it, _, hfeas_it, _, _, _, hpar_it⟩ := h
  unfold selectParentsProg
  refine ⟨⟨h1, hsafe_it⟩, validHistory_bind_step hvh_it (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc_it,
    by simp only [client_simps]; exact hfr_it,
    fun x hx => by simpa [client_simps] using hmod_it x hx,
    ?_, ?_⟩
  · simp only [client_simps]
    rw [hfeas_it, htake]
    unfold selectParents
    have hopts : (Vector.ofFn optFn) =
        (Vector.ofFn fun v : Fin n =>
          if v = r then some r
          else argMinFin n (fun w => a[v.1][w.1] && w != v) (fun w => c[v.1][w.1])) := rfl
    simp [← hopts]
  · intro v
    simp only [client_simps]
    rw [hpar_it v v.isLt]
    simp [selectParents, optFn]

private theorem hasCycleFromProg_spec {w n parentBase : ℕ} (x : Fin n) (f : ParentTable n)
    (s₀ : Memory.State) (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_n : Fits w n)
    (hp_f : parentBase + n ≤ s₀.frontier)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.1) = (f[v.1]).1) :
    iterationSafe hasCycleStep HasCycleStepSafe w ⟨n, parentBase, x.1⟩ n ⟨0, x.1, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (hasCycleFromProg ⟨n, parentBase, x.1⟩)) ∧
      memoryCost (hasCycleFromProg ⟨n, parentBase, x.1⟩) s₀ ≤ n ∧
      (Memory.spec 0).clientState s₀ (hasCycleFromProg ⟨n, parentBase, x.1⟩) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (hasCycleFromProg ⟨n, parentBase, x.1⟩) =
        (if hasCycleFrom x f then 1 else 0) := by
  have h := iterate_spec hasCycleStep HasCycleStepSafe w ⟨n, parentBase, x.1⟩ 1 n
    (fun m st s =>
      let curFin := (fun i : Fin n => f[i.1])^[m] x
      let hitBool := (List.range m).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x
      st.step = m ∧ st.cur = curFin.1 ∧ st.hit = (if hitBool then 1 else 0) ∧ s = s₀)
    (fun _ => False)
    (fun m hm st s ⟨hst, hcur, hhit, hs⟩ => by
      rcases st with ⟨step, cur, hit⟩
      dsimp only at hst hcur hhit
      subst step s
      set curFin : Fin n := (fun i : Fin n => f[i.1])^[m] x
      have hcur_lt : cur < n := hcur ▸ curFin.isLt
      have hmem_cur : s₀.mem (parentBase + cur) = (f[curFin.1]).1 := by
        rw [hcur]
        exact hf_mem curFin
      refine ⟨by dsimp only [HasCycleStepSafe]; exact ⟨h1, hfit_p.of_le (by omega),
          hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, fun _ _ => ?_, ?_⟩
      · unfold hasCycleStep
        dsimp only
        exact validHistory_read_bind (by omega) (by split_ifs <;> trivial)
      · unfold hasCycleStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read]
        split_ifs <;> simp [client_simps]
      · unfold hasCycleStep
        dsimp only
        simp [client_simps]
      · unfold hasCycleStep
        dsimp only
        simp [client_simps]
      · unfold hasCycleStep
        dsimp only
        simp only [client_simps, hmem_cur, List.range_succ, List.any_append, List.any_cons,
          List.any_nil, Bool.or_false]
        generalize
          ((List.range m).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x) = prev at hhit ⊢
        simp only [Function.iterate_succ_apply']
        subst hhit
        cases prev
        · by_cases heq : f[curFin.1] = x
          · simp [heq, curFin, client_simps]
          · have hval : (f[curFin.1]).1 ≠ x.1 := fun h => heq (Fin.ext h)
            simp [heq, hval, curFin, client_simps]
        · simp [curFin, client_simps])
    ⟨0, x.1, 0⟩ s₀ ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hsafe, hvh, hmc, _, _, _, _, hhit_n, hs_n⟩ := h
  unfold hasCycleFromProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp [client_simps, hs_n],
    ?_⟩
  simp only [client_simps]
  exact hhit_n.trans (by rw [hasCycleFrom_eq])

private theorem findCycleProg_spec {w n parentBase : ℕ} (r : Fin n) (f : ParentTable n)
    (s₀ : Memory.State) (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_n : Fits w n)
    (hf0 : 0 < s₀.frontier) (hp_f : parentBase + n ≤ s₀.frontier)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.1) = (f[v.1]).1) :
    iterationSafe findCycleOuterStep FindCycleOuterStepSafe w ⟨n, r.1, parentBase⟩ n ⟨0, n⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (findCycleProg ⟨n, r.1, parentBase⟩)) ∧
      memoryCost (findCycleProg ⟨n, r.1, parentBase⟩) s₀ ≤ (n + 1) * n ∧
      (Memory.spec 0).clientState s₀ (findCycleProg ⟨n, r.1, parentBase⟩) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (findCycleProg ⟨n, r.1, parentBase⟩) =
        optFinIdx (findCycleTable r f) := by
  let stepFn := fun (acc : Option (Fin n)) (x : Fin n) =>
    match acc with
    | some x0 => some x0
    | none => if x == r then none else if hasCycleFrom x f then some x else none
  have h := iterate_spec findCycleOuterStep FindCycleOuterStepSafe w ⟨n, r.1, parentBase⟩
    (n + 1) n
    (fun m st s =>
      let acc := ((List.finRange n).take m).foldl stepFn none
      st.v = m ∧ st.found = optFinIdx acc ∧ s = s₀)
    (fun _ => False)
    (fun m hm st s ⟨hv, hfd, hs⟩ => by
      rcases st with ⟨vIdx, foundIdx⟩
      dsimp only at hv hfd
      subst vIdx s
      set vFin : Fin n := ⟨m, hm⟩
      have hcyc := hasCycleFromProg_spec vFin f s₀ h1 hfit_p hfit_n hp_f hf_mem
      refine ⟨by dsimp only [FindCycleOuterStepSafe]; exact ⟨h1, hfit_n.of_le (by omega), hcyc.1⟩,
        ?_, ?_, ?_, fun _ _ => ?_, ?_⟩
      · unfold findCycleOuterStep
        refine validHistory_read_bind hf0 ?_
        dsimp only
        split_ifs
        · exact validHistory_pure w _ _
        · exact validHistory_pure w _ _
        · refine validHistory_bind_step hcyc.2.1 ?_
          rw [hcyc.2.2.2.1]
          split_ifs <;> exact validHistory_pure w _ _
      · unfold findCycleOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read]
        split_ifs
        · simp only [client_simps]; omega
        · simp only [client_simps]; omega
        · rw [memoryCost_bind', hcyc.2.2.2.1]
          have hc_le : memoryCost (hasCycleFromProg ⟨n, parentBase, m⟩) s₀ ≤ n := hcyc.2.2.1
          split_ifs <;> simp only [client_simps] <;> omega
      · unfold findCycleOuterStep
        dsimp only
        have hc_s := hcyc.2.2.2.1
        dsimp only [vFin] at hc_s
        simp [client_simps, hc_s]
      · unfold findCycleOuterStep
        dsimp only
        have hc_s := hcyc.2.2.2.1
        dsimp only [vFin] at hc_s
        simp [client_simps, hc_s]
      · rw [foldl_take_finRange_succ hm stepFn none]
        generalize hacc : ((List.finRange n).take m).foldl stepFn none = acc at hfd ⊢
        dsimp only [stepFn]
        unfold findCycleOuterStep
        dsimp only
        simp only [client_simps]
        cases acc with
        | some x0 =>
          have hflt : foundIdx < n := by rw [hfd]; exact x0.isLt
          simp only [hflt, ↓reduceIte, client_simps, optFinIdx]
          exact ⟨trivial, hfd, trivial⟩
        | none =>
          have hfn : ¬(foundIdx < n) := by rw [hfd, optFinIdx]; omega
          simp only [hfn, ↓reduceIte]
          by_cases hmr : m = r.1
          · have hvr : ((⟨r.1, hmr ▸ hm⟩ : Fin n) == r) = true := beq_iff_eq.mpr (Fin.ext rfl)
            simp only [hmr, hvr, ↓reduceIte, client_simps, optFinIdx]
            exact ⟨trivial, trivial, trivial⟩
          · have hvr : (⟨m, hm⟩ == r) = false :=
              beq_false_of_ne (fun h => hmr (congrArg Fin.val h))
            have hc_s : (Memory.spec 0).clientState s₀ (hasCycleFromProg ⟨n, parentBase, m⟩) =
                s₀ := hcyc.2.2.2.1
            have hc_r : (Memory.spec 0).clientResult s₀ (hasCycleFromProg ⟨n, parentBase, m⟩) =
                if hasCycleFrom ⟨m, hm⟩ f then 1 else 0 := hcyc.2.2.2.2
            simp only [hmr, hvr, Bool.false_eq_true, ↓reduceIte, hc_s, hc_r]
            cases hh : hasCycleFrom ⟨m, hm⟩ f
            · simp only [Bool.false_eq_true, Nat.zero_ne_one, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, trivial⟩
            · simp only [↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, trivial⟩)
    ⟨0, n⟩ s₀ ⟨rfl, rfl, rfl⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe, hvh, hmc, _, _, _, hfd_n, hs_n⟩ := h
  unfold findCycleProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp [client_simps, hs_n],
    ?_⟩
  simp only [client_simps]
  exact hfd_n.trans (by rw [htake]; rfl)

private theorem cycleMaskProg_spec {w n parentBase maskBase : ℕ} (f : ParentTable n)
    (x0 : Fin n) (s₀ : Memory.State)
    (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_m : Fits w (maskBase + n))
    (hfit_n : Fits w n) (hp_f : parentBase + n ≤ s₀.frontier) (hm_f : maskBase + n ≤ s₀.frontier)
    (hdisj : parentBase + n ≤ maskBase ∨ maskBase + n ≤ parentBase)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.1) = (f[v.1]).1) :
    let cm : CycleMaskArgs := ⟨n, parentBase, maskBase, x0.1⟩
    let s0z := (Memory.spec 0).clientState s₀ (zeroWordsProg ⟨maskBase, n⟩)
    let s' := (Memory.spec 0).clientState s₀ (cycleMaskProg cm)
    (iterationSafe zeroStep ZeroStepSafe w ⟨maskBase, n⟩ n 0 s₀ ∧
      iterationSafe cycleMaskStep CycleMaskStepSafe w cm n ⟨0, x0.1⟩ s0z) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (cycleMaskProg cm)) ∧
      memoryCost (cycleMaskProg cm) s₀ ≤ 3 * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(maskBase ≤ addr ∧ addr < maskBase + n) → s'.mem addr = s₀.mem addr) ∧
      (∀ y : Fin n, s'.mem (maskBase + y.1) = if (cycleMask f x0)[y.1] then 1 else 0) := by
  let cm : CycleMaskArgs := ⟨n, parentBase, maskBase, x0.1⟩
  have hzero := zeroWordsProg_spec ⟨maskBase, n⟩ s₀ hm_f hfit_m hfit_n
  set s0z := (Memory.spec 0).clientState s₀ (zeroWordsProg ⟨maskBase, n⟩)
  have hf_mem_z : ∀ v : Fin n, s0z.mem (parentBase + v.1) = (f[v.1]).1 := by
    intro v
    rw [hzero.2.2.2.2.1 _ (by dsimp only; have := v.isLt; omega)]
    exact hf_mem v
  have hloop := iterate_spec cycleMaskStep CycleMaskStepSafe w cm 2 n
    (fun m st s =>
      st.step = m ∧ st.cur = ((fun i : Fin n => f[i.1])^[m] x0).1 ∧
        s.frontier = s0z.frontier ∧
        (∀ v : Fin n, s.mem (parentBase + v.1) = (f[v.1]).1) ∧
        (∀ y : Fin n, s.mem (maskBase + y.1) =
          if ∃ j < m, (fun i : Fin n => f[i.1])^[j] x0 = y then 1 else 0))
    (fun addr => maskBase ≤ addr ∧ addr < maskBase + n)
    (fun m hm st s ⟨hst, hcur, hfr, hpar_s, hmask_s⟩ => by
      rcases st with ⟨step, cur⟩
      dsimp only at hst hcur
      subst step
      set curFin : Fin n := (fun i : Fin n => f[i.1])^[m] x0
      have hcur_lt : cur < n := hcur ▸ curFin.isLt
      have hmem_cur : s.mem (parentBase + cur) = (f[curFin.1]).1 := by
        rw [hcur]
        exact hpar_s curFin
      refine ⟨by dsimp only [CycleMaskStepSafe, cm]; exact ⟨h1, hfit_p.of_le (by omega),
          hfit_m.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold cycleMaskStep
        dsimp only [cm]
        exact validHistory_read_bind (by rw [hfr, hzero.2.2.2.1]; omega)
          (validHistory_write_bind (by rw [hfr, hzero.2.2.2.1]; omega) h1
            (validHistory_pure w _ _))
      · unfold cycleMaskStep
        dsimp only [cm]
        rw [memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [cycleMaskStep, cm, client_simps]
      · intro addr haddr
        simp only [cycleMaskStep, cm, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp only [cycleMaskStep, cm, client_simps, hmem_cur, Function.iterate_succ_apply']
        refine ⟨trivial, rfl, hfr, ?_, ?_⟩
        · intro v
          rw [Function.update_of_ne (by have := v.isLt; omega)]
          exact hpar_s v
        · intro y
          by_cases hcy : y.1 = cur
          · have hy_eq : (fun i : Fin n => f[i.1])^[m] x0 = y := Fin.ext (hcur.symm.trans hcy.symm)
            have hex : ∃ j < m + 1, (fun i : Fin n => f[i.1])^[j] x0 = y :=
              ⟨m, Nat.lt_succ_self m, hy_eq⟩
            rw [hcy, Function.update_self, ite_eq_left hex]
          · rw [Function.update_of_ne (by omega), hmask_s y]
            have hiff : (∃ j < m + 1, (fun i : Fin n => f[i.1])^[j] x0 = y) ↔
                (∃ j < m, (fun i : Fin n => f[i.1])^[j] x0 = y) := by
              refine ⟨?_, fun ⟨j, hj, h⟩ => ⟨j, Nat.lt_succ_of_lt hj, h⟩⟩
              rintro ⟨j, hj, h⟩
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
              · exact ⟨j, hlt, h⟩
              · exact absurd (hcur.trans (congrArg Fin.val h)).symm hcy
            rw [if_congr hiff rfl rfl])
    ⟨0, x0.1⟩ s0z
    ⟨rfl, rfl, rfl, hf_mem_z, fun y => by
      simp [hzero.2.2.2.2.2 y.1 y.isLt]⟩
  unfold cycleMaskProg cycleMaskLoopProg
  refine ⟨⟨hzero.1, hloop.1⟩,
    validHistory_bind_step hzero.2.1
      (validHistory_bind_step hloop.2.1 (validHistory_pure w _ _)),
    by
      rw [memoryCost_bind', memoryCost_bind']
      have hz_c := hzero.2.2.1
      have hl_c := hloop.2.2.1
      dsimp only [cm, s0z] at hz_c hl_c ⊢
      simp only [client_simps] at hz_c hl_c ⊢
      omega,
    by
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      simp only [client_simps]
      exact hloop.2.2.2.1.trans hzero.2.2.2.1,
    fun addr haddr => by
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      simp only [client_simps]
      exact (hloop.2.2.2.2.1 addr haddr).trans (hzero.2.2.2.2.1 addr haddr),
    fun y => by
      obtain ⟨_, _, _, _, _, _, _, _, _, hmask_n⟩ := hloop
      simp only [client_simps]
      rw [hmask_n y]
      by_cases hcy : (cycleMask f x0)[y.1] = true
      · simp [hcy, (getElem_cycleMask f x0 y).mp hcy]
      · have hnot : ¬∃ j < n, (fun i : Fin n => f[i.1])^[j] x0 = y :=
          mt (getElem_cycleMask f x0 y).mpr hcy
        simp [hcy, hnot]⟩

/-! ### Edmonds §4 reduced exit costs and row-potential equivalence -/

private theorem argMinFin_of_lt_iff {β γ : Type*} [LinearOrder β] [LinearOrder γ] {n : ℕ}
    (pred : Fin n → Bool) (f : Fin n → β) (g : Fin n → γ)
    (h : ∀ x y, pred x = true → pred y = true → (f x < f y ↔ g x < g y)) :
    argMinFin n pred f = argMinFin n pred g := by
  unfold argMinFin
  suffices ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ y, acc = some y → pred y = true) →
      l.foldl (fun a i => if pred i then List.argAux (fun x y => f x < f y) a i else a) acc =
        l.foldl (fun a i => if pred i then List.argAux (fun x y => g x < g y) a i else a) acc from
    this (List.finRange n) none (fun _ h => by cases h)
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons i ls ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    cases hp : pred i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih acc hacc
    · simp only [↓reduceIte]
      have harg_eq : List.argAux (fun x y => f x < f y) acc i =
          List.argAux (fun x y => g x < g y) acc i := by
        cases acc with
        | none => rfl
        | some z => simp [List.argAux, h i z hp (hacc z rfl)]
      rw [harg_eq]
      refine ih _ fun y hy => ?_
      cases acc with
      | none =>
        simp only [List.argAux, Option.some.injEq] at hy
        exact hy ▸ hp
      | some z =>
        simp only [List.argAux] at hy
        split_ifs at hy <;> simp only [Option.some.injEq] at hy
        · exact hy ▸ hp
        · exact hacc y (congrArg some hy)

private theorem argMinFin_spec {β : Type*} [LinearOrder β] {n : ℕ} (pred : Fin n → Bool)
    (val : Fin n → β) {x : Fin n} (hx : argMinFin n pred val = some x) :
    pred x = true ∧ ∀ y : Fin n, pred y = true → val x ≤ val y := by
  have hgen : ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ a, acc = some a → pred a = true) →
      ∀ x, l.foldl (fun a i => if pred i then List.argAux (fun u v => val u < val v) a i else a)
        acc = some x →
      pred x = true ∧ (∀ a, acc = some a → val x ≤ val a) ∧
        ∀ y ∈ l, pred y = true → val x ≤ val y := by
    intro l
    induction l with
    | nil =>
      intro acc hacc x hx'
      simp only [List.foldl_nil] at hx'
      exact ⟨hacc x hx', fun a ha => by rw [hx'] at ha; cases ha; exact le_rfl,
        fun _ hy => by cases hy⟩
    | cons i ls ih =>
      intro acc hacc x hx'
      simp only [List.foldl_cons] at hx'
      cases hp : pred i
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hx'
        obtain ⟨hpx, hacc_le, hls_le⟩ := ih acc hacc x hx'
        refine ⟨hpx, hacc_le, fun y hy hpy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hmem
        · simp [hp] at hpy
        · exact hls_le y hmem hpy
      · simp only [hp, ↓reduceIte] at hx'
        have hacc' : ∀ a,
            List.argAux (fun u v => val u < val v) acc i = some a → pred a = true := by
          intro a ha
          cases acc with
          | none => simp only [List.argAux, Option.some.injEq] at ha; exact ha ▸ hp
          | some z =>
            simp only [List.argAux] at ha
            split_ifs at ha <;> simp only [Option.some.injEq] at ha
            · exact ha ▸ hp
            · exact hacc a (congrArg some ha)
        obtain ⟨hpx, hacc'_le, hls_le⟩ := ih _ hacc' x hx'
        refine ⟨hpx, ?_, ?_⟩
        · intro a ha
          subst ha
          by_cases hlt : val i < val a
          · exact (hacc'_le i (by simp [List.argAux, hlt])).trans (le_of_lt hlt)
          · exact hacc'_le a (by simp [List.argAux, hlt])
        · intro y hy hpy
          rcases List.mem_cons.mp hy with rfl | hmem
          · cases acc with
            | none => exact hacc'_le y rfl
            | some a =>
              by_cases hlt : val y < val a
              · exact hacc'_le y (by simp [List.argAux, hlt])
              · exact (hacc'_le a (by simp [List.argAux, hlt])).trans (le_of_not_gt hlt)
          · exact hls_le y hmem hpy
  obtain ⟨hpx, _, hall⟩ := hgen (List.finRange n) none (fun _ h => by cases h) x hx
  exact ⟨hpx, fun y hpy => hall y (List.mem_finRange y) hpy⟩

private theorem foldl_and_eq_true {α : Type*} (p : α → Bool) (l : List α) (b : Bool) :
    l.foldl (fun acc x => acc && p x) b = true ↔ b = true ∧ ∀ x ∈ l, p x = true := by
  induction l generalizing b with
  | nil => simp
  | cons x ls ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨hb, hpx⟩, hls⟩
      exact ⟨hb, fun y hy => by rcases hy with rfl | hmem; exacts [hpx, hls y hmem]⟩
    · rintro ⟨hb, hall⟩
      exact ⟨⟨hb, hall x (Or.inl rfl)⟩, fun y hy => hall y (Or.inr hy)⟩

private theorem selectParents_feasible_spec {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (r : Fin n) (hfeas : (selectParents a c r).feasible = true) :
    let f := (selectParents a c r).parents
    f[r.1] = r ∧
      ∀ v : Fin n, v ≠ r →
        a[v.1][(f[v.1]).1] = true ∧ f[v.1] ≠ v ∧
          ∀ w : Fin n, a[v.1][w.1] = true → w ≠ v → c[v.1][(f[v.1]).1] ≤ c[v.1][w.1] := by
  unfold selectParents at hfeas ⊢
  dsimp only at hfeas ⊢
  rw [foldl_and_eq_true] at hfeas
  refine ⟨by simp, fun v hvr => ?_⟩
  have hsome := hfeas.2 v (List.mem_finRange v)
  simp only [Vector.getElem_ofFn, Fin.eta, hvr, ↓reduceIte] at hsome ⊢
  obtain ⟨fv, harg⟩ := Option.isSome_iff_exists.mp hsome
  have hfv : (argMinFin n (fun w => a[v.1][w.1] && w != v) (fun w => c[v.1][w.1])).getD v = fv := by
    rw [harg]; rfl
  obtain ⟨hpred, hmin⟩ := argMinFin_spec _ _ harg
  simp only [Bool.and_eq_true, bne_iff_ne] at hpred
  simp only [hfv]
  exact ⟨hpred.1, hpred.2, fun w haw hne => hmin w (by simp [haw, hne])⟩

private theorem findCycleTable_spec {n : ℕ} (r : Fin n) (f : ParentTable n) {x0 : Fin n}
    (hx0 : findCycleTable r f = some x0) : x0 ≠ r ∧ hasCycleFrom x0 f = true := by
  have hgen : ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (∀ y, acc = some y → y ≠ r ∧ hasCycleFrom y f = true) →
      ∀ x0, l.foldl (fun acc x => match acc with
        | some a => some a
        | none => if x == r then none else if hasCycleFrom x f then some x else none)
        acc = some x0 →
      x0 ≠ r ∧ hasCycleFrom x0 f = true := by
    intro l
    induction l with
    | nil => intro acc hacc x0 hx; exact hacc x0 hx
    | cons x ls ih =>
      intro acc hacc x0 hx
      simp only [List.foldl_cons] at hx
      cases acc with
      | some a => exact ih (some a) hacc x0 hx
      | none =>
        refine ih _ (fun y hy => ?_) x0 hx
        by_cases hxr : x == r
        · simp [hxr] at hy
        · simp only [hxr, Bool.false_eq_true, ↓reduceIte] at hy
          by_cases hcy : hasCycleFrom x f = true
          · simp only [hcy, ↓reduceIte, Option.some.injEq] at hy
            subst hy
            exact ⟨by simpa [beq_iff_eq] using hxr, hcy⟩
          · simp [hcy] at hy
  exact hgen (List.finRange n) none (fun _ h => by cases h) x0 hx0

private theorem not_inCycle_root {n : ℕ} (r : Fin n) (f : ParentTable n) {x0 : Fin n}
    (hfr : f[r.1] = r) (hx0 : findCycleTable r f = some x0) :
    (cycleMask f x0)[x0.1] = true ∧ ∀ x : Fin n, (cycleMask f x0)[x.1] = true → x ≠ r := by
  refine ⟨(getElem_cycleMask f x0 x0).mpr ⟨0, r.pos, rfl⟩, ?_⟩
  obtain ⟨hx0_ne, hcy⟩ := findCycleTable_spec r f hx0
  rw [hasCycleFrom_eq] at hcy
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at hcy
  obtain ⟨t, _, ht⟩ := hcy
  let g : Fin n → Fin n := fun i => f[i.1]
  have hfix : ∀ m, g^[m] r = r := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih]; exact hfr
  have hper : ∀ q, g^[q * (t + 1)] x0 = x0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih]
      exact ht
  intro x hx hxr
  subst hxr
  obtain ⟨j, _, hj⟩ := (getElem_cycleMask f x0 x).mp hx
  have hjle : j ≤ (j + 1) * (t + 1) := by nlinarith
  have hxeq : x0 = x := by
    calc x0 = g^[(j + 1) * (t + 1)] x0 := (hper (j + 1)).symm
      _ = g^[((j + 1) * (t + 1) - j) + j] x0 := by rw [Nat.sub_add_cancel hjle]
      _ = g^[(j + 1) * (t + 1) - j] (g^[j] x0) := Function.iterate_add_apply _ _ _ _
      _ = g^[(j + 1) * (t + 1) - j] x := by rw [hj]
      _ = x := hfix _
  exact hx0_ne hxeq

/-- Row-potential equivalence between an unreduced cost table `cUnred` and a reduced cost table
`cRed` on active arcs of `a`. -/
private def RowPotEq {n : ℕ} (a : AdjTable n) (cUnred cRed : CostTable ℤ n) : Prop :=
  ∃ φ : Fin n → ℤ, ∀ u w : Fin n, a[u.1][w.1] = true → cUnred[u.1][w.1] = cRed[u.1][w.1] + φ u

private def cycleSum {n : ℕ} (c : CostTable ℤ n) (f : ParentTable n)
    (inCycle : Vector Bool n) : ℤ :=
  (List.finRange n).foldl (fun acc y => if inCycle[y.1] then acc + c[y.1][f[y.1].1] else acc) 0

private def reducedBestExitTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n) : Vector (Option (Fin n)) n :=
  Vector.ofFn fun w : Fin n =>
    argMinFin n (fun x => inCycle[x.1] && a[x.1][w.1])
      (fun x => c[x.1][w.1] - c[x.1][f[x.1].1])

private def contractReducedCostTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (x0 : Fin n) : CostTable ℤ n :=
  Vector.ofFn fun u : Fin n => Vector.ofFn fun w : Fin n =>
    if inCycle[u.1] then
      if u == x0 then
        if !(inCycle[w.1]) then
          match bExit[w.1] with
          | some x => c[x.1][w.1] - c[x.1][f[x.1].1]
          | none => 0
        else 0
      else 0
    else
      if inCycle[w.1] then
        if w == x0 then
          match bEntry[u.1] with
          | some y => c[u.1][y.1]
          | none => 0
        else 0
      else if a[u.1][w.1] then c[u.1][w.1]
      else 0

private theorem getElem_contractReducedCostTable {n : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (x0 u w : Fin n) :
    (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][w.1] =
      if inCycle[u.1] then
        if u == x0 then
          if !(inCycle[w.1]) then
            match bExit[w.1] with
            | some x => c[x.1][w.1] - c[x.1][f[x.1].1]
            | none => 0
          else 0
        else 0
      else
        if inCycle[w.1] then
          if w == x0 then
            match bEntry[u.1] with
            | some y => c[u.1][y.1]
            | none => 0
          else 0
        else if a[u.1][w.1] then c[u.1][w.1]
        else 0 := by
  simp [contractReducedCostTable]

private theorem otherCycleCost_add_self {n : ℕ} (c : CostTable ℤ n) (f : ParentTable n)
    (inCycle : Vector Bool n) {x : Fin n} (hx : inCycle[x.1] = true) :
    c[x.1][f[x.1].1] + (otherCycleCost c f inCycle)[x.1] = cycleSum c f inCycle := by
  have hshift : ∀ (l : List (Fin n)) (p : Fin n → Bool) (val : Fin n → ℤ) (a b : ℤ),
      l.foldl (fun acc y => if p y then acc + val y else acc) (a + b) =
        a + l.foldl (fun acc y => if p y then acc + val y else acc) b := by
    intro l p val
    induction l with
    | nil => intro _ _; rfl
    | cons y ls ih =>
      intro a b
      simp only [List.foldl_cons]
      split_ifs
      · rw [add_assoc, ih]
      · exact ih a b
  have hnotmem : ∀ (l : List (Fin n)) (init : ℤ), x ∉ l →
      l.foldl (fun acc y => if inCycle[y.1] && y != x then acc + c[y.1][f[y.1].1] else acc) init =
        l.foldl (fun acc y => if inCycle[y.1] then acc + c[y.1][f[y.1].1] else acc) init := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons y ls ih =>
      intro init hmem
      simp only [List.mem_cons, not_or] at hmem
      have hne : (y != x) = true := bne_iff_ne.mpr (Ne.symm hmem.1)
      simp only [List.foldl_cons, hne, Bool.and_true]
      exact ih _ hmem.2
  have hmem : ∀ (l : List (Fin n)) (init : ℤ), l.Nodup → x ∈ l →
      c[x.1][f[x.1].1] +
        l.foldl (fun acc y => if inCycle[y.1] && y != x then acc + c[y.1][f[y.1].1] else acc)
          init =
        l.foldl (fun acc y => if inCycle[y.1] then acc + c[y.1][f[y.1].1] else acc) init := by
    intro l
    induction l with
    | nil => intro _ _ hm; cases hm
    | cons y ls ih =>
      intro init hnd hm
      rw [List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with rfl | hls
      · simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hx]
        rw [hnotmem ls init hnd.1, ← hshift ls _ _ c[x.1][f[x.1].1] init, add_comm]
      · have hne : (y != x) = true := bne_iff_ne.mpr (fun heq => hnd.1 (heq ▸ hls))
        simp only [hne, Bool.and_true]
        exact ih _ hnd.2 hls
  unfold otherCycleCost cycleSum
  simp only [Vector.getElem_ofFn, hx, ↓reduceIte]
  exact hmem (List.finRange n) 0 (List.nodup_finRange n) (List.mem_finRange x)

private theorem selectParents_of_rowPotEq {n : ℕ} {a : AdjTable n} {cUnred cRed : CostTable ℤ n}
    (r : Fin n) (hpot : RowPotEq a cUnred cRed) :
    selectParents a cRed r = selectParents a cUnred r := by
  obtain ⟨φ, hφ⟩ := hpot
  unfold selectParents
  have hopts :
      (Vector.ofFn fun v : Fin n =>
        if v = r then some r
        else argMinFin n (fun w => a[v.1][w.1] && w != v) (fun w => cRed[v.1][w.1])) =
      (Vector.ofFn fun v : Fin n =>
        if v = r then some r
        else argMinFin n (fun w => a[v.1][w.1] && w != v) (fun w => cUnred[v.1][w.1])) := by
    apply Vector.ext
    intro v hv
    simp only [Vector.getElem_ofFn]
    split_ifs
    · rfl
    · exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
        simp only [Bool.and_eq_true] at hx hy
        have h1 := hφ ⟨v, hv⟩ x hx.1
        have h2 := hφ ⟨v, hv⟩ y hy.1
        dsimp only at h1 h2
        omega
  simp only [hopts]

private theorem bestEntryTable_of_rowPotEq {n : ℕ} {a : AdjTable n} {cUnred cRed : CostTable ℤ n}
    (inCycle : Vector Bool n) (hpot : RowPotEq a cUnred cRed) :
    bestEntryTable a cRed inCycle = bestEntryTable a cUnred inCycle := by
  obtain ⟨φ, hφ⟩ := hpot
  unfold bestEntryTable
  apply Vector.ext
  intro u hu
  simp only [Vector.getElem_ofFn]
  exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    have h1 := hφ ⟨u, hu⟩ x hx.2
    have h2 := hφ ⟨u, hu⟩ y hy.2
    dsimp only at h1 h2
    omega

private theorem exitCost_eq_reduced_add_cycleSum {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    (hpot : RowPotEq a cUnred cRed)
    (hact : ∀ x : Fin n, inCycle[x.1] = true → a[x.1][f[x.1].1] = true)
    {x w : Fin n} (hx : inCycle[x.1] = true) (haw : a[x.1][w.1] = true) :
    cUnred[x.1][w.1] + (otherCycleCost cUnred f inCycle)[x.1] =
      (cRed[x.1][w.1] - cRed[x.1][f[x.1].1]) + cycleSum cUnred f inCycle := by
  obtain ⟨φ, hφ⟩ := hpot
  have hsum := otherCycleCost_add_self cUnred f inCycle hx
  have h1 := hφ x w haw
  have h2 := hφ x f[x.1] (hact x hx)
  omega

private theorem reducedBestExitTable_eq_bestExitTable {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    (hpot : RowPotEq a cUnred cRed)
    (hact : ∀ x : Fin n, inCycle[x.1] = true → a[x.1][f[x.1].1] = true) :
    reducedBestExitTable a cRed f inCycle =
      bestExitTable a cUnred inCycle (otherCycleCost cUnred f inCycle) := by
  unfold reducedBestExitTable bestExitTable
  apply Vector.ext
  intro w hw
  simp only [Vector.getElem_ofFn]
  exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
    simp only [Bool.and_eq_true] at hx hy
    have h1 := exitCost_eq_reduced_add_cycleSum hpot hact (w := ⟨w, hw⟩) hx.1 hx.2
    have h2 := exitCost_eq_reduced_add_cycleSum hpot hact (w := ⟨w, hw⟩) hy.1 hy.2
    dsimp only at h1 h2
    omega

private theorem rowPotEq_contractReduced {n : ℕ} {a : AdjTable n}
    {cUnred cRed : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    {x0 r : Fin n} (hpot : RowPotEq a cUnred cRed) (hx0_in : inCycle[x0.1] = true)
    (hact : ∀ x : Fin n, inCycle[x.1] = true → a[x.1][f[x.1].1] = true) :
    let other := otherCycleCost cUnred f inCycle
    let bEntry := bestEntryTable a cRed inCycle
    let bExit := reducedBestExitTable a cRed f inCycle
    RowPotEq (contractAdjTable a inCycle bEntry bExit x0 r)
      (contractCostTable cUnred inCycle other bEntry bExit x0)
      (contractReducedCostTable a cRed f inCycle bEntry bExit x0) := by
  obtain ⟨φ, hφ⟩ := hpot
  refine ⟨fun u => if inCycle[u.1] then (if u = x0 then cycleSum cUnred f inCycle else 0) else φ u,
    fun u w ha' => ?_⟩
  rw [getElem_contractAdjTable] at ha'
  rw [getElem_contractCostTable, getElem_contractReducedCostTable]
  by_cases hu : inCycle[u.1] = true
  · simp only [hu, ↓reduceIte] at ha' ⊢
    by_cases hux : u = x0
    · subst hux
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at ha' ⊢
      obtain ⟨hw_out, hbx_some⟩ := ha'
      simp only [hw_out, ↓reduceIte]
      cases hbx : (reducedBestExitTable a cRed f inCycle)[w.1] with
      | none => simp [hbx] at hbx_some
      | some x =>
        have hbx' : argMinFin n (fun z => inCycle[z.1] && a[z.1][w.1])
            (fun z => cRed[z.1][w.1] - cRed[z.1][f[z.1].1]) = some x := by
          simpa [reducedBestExitTable] using hbx
        obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbx'
        simp only [Bool.and_eq_true] at hpred
        exact exitCost_eq_reduced_add_cycleSum ⟨φ, hφ⟩ hact hpred.1 hpred.2
    · have hux_b : (u == x0) = false := beq_false_of_ne hux
      simp [hux, hux_b]
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at ha' ⊢
    by_cases hw : inCycle[w.1] = true
    · simp only [hw, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at ha' ⊢
      obtain ⟨rfl, hbe_some⟩ := ha'
      simp only [↓reduceIte]
      cases hbe : (bestEntryTable a cRed inCycle)[u.1] with
      | none => simp [hbe] at hbe_some
      | some y =>
        have hbe' : argMinFin n (fun z => inCycle[z.1] && a[u.1][z.1])
            (fun z => cRed[u.1][z.1]) = some y := by
          simpa [bestEntryTable] using hbe
        obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbe'
        simp only [Bool.and_eq_true] at hpred
        exact hφ u y hpred.2
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at ha' ⊢
      have hwx : w ≠ x0 := fun heq => hw (heq ▸ hx0_in)
      have hwx_b : (w == x0) = false := beq_false_of_ne hwx
      simp only [hwx_b, Bool.false_eq_true, ↓reduceIte, ha']
      exact hφ u w ha'

private theorem contractReducedCostTable_bounds {n k M₀ : ℕ} {a : AdjTable n}
    {c : CostTable ℤ n} {f : ParentTable n} {inCycle : Vector Bool n}
    {bEntry : Vector (Option (Fin n)) n} {x0 : Fin n}
    (hbnd : ∀ u w : Fin n, -(M₀ : ℤ) ≤ c[u.1][w.1] ∧ c[u.1][w.1] ≤ (k + 1 : ℤ) * M₀)
    (hopt : ∀ x : Fin n, inCycle[x.1] = true →
      ∀ w : Fin n, a[x.1][w.1] = true → w ≠ x → c[x.1][f[x.1].1] ≤ c[x.1][w.1])
    (u w : Fin n) :
    let bExit := reducedBestExitTable a c f inCycle
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    (-(M₀ : ℤ) ≤ c'[u.1][w.1] ∧ c'[u.1][w.1] ≤ (k + 2 : ℤ) * M₀) := by
  dsimp only
  rw [getElem_contractReducedCostTable]
  have hzero : -(M₀ : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (k + 2 : ℤ) * M₀ := ⟨by omega, by positivity⟩
  have hle_step : ∀ x y : Fin n, -(M₀ : ℤ) ≤ c[x.1][y.1] ∧ c[x.1][y.1] ≤ (k + 2 : ℤ) * M₀ := by
    intro x y
    obtain ⟨hlo, hhi⟩ := hbnd x y
    exact ⟨hlo, by nlinarith only [hhi]⟩
  split_ifs with hu hux hw_out hw hwx haw
  · cases hbx : (reducedBestExitTable a c f inCycle)[w.1] with
    | none => exact hzero
    | some x =>
      have hbx' : argMinFin n (fun z => inCycle[z.1] && a[z.1][w.1])
          (fun z => c[z.1][w.1] - c[z.1][f[z.1].1]) = some x := by
        simpa [reducedBestExitTable] using hbx
      obtain ⟨hpred, _⟩ := argMinFin_spec _ _ hbx'
      simp only [Bool.and_eq_true] at hpred
      have hwx_ne : w ≠ x := by
        intro heq
        subst heq
        simp [hpred.1] at hw_out
      have hnonneg : c[x.1][f[x.1].1] ≤ c[x.1][w.1] := hopt x hpred.1 w hpred.2 hwx_ne
      obtain ⟨_, hhi_w⟩ := hbnd x w
      obtain ⟨hlo_f, _⟩ := hbnd x f[x.1]
      have hM0 : (0 : ℤ) ≤ M₀ := Int.natCast_nonneg M₀
      dsimp only
      exact ⟨by linarith only [hM0, hnonneg], by linarith only [hhi_w, hlo_f]⟩
  · exact hzero
  · exact hzero
  · cases bEntry[u.1] with
    | none => exact hzero
    | some y => exact hle_step u y
  · exact hzero
  · exact hle_step u w
  · exact hzero

private theorem fillBestEntryRowProg_spec {w n ws k : ℕ} (uFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (inCycle : Vector Bool n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1])) :
    let rowArgs : BestEntryRowArgs :=
      ⟨n, uFin.1, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
        candPredBase ws n, candCostBase ws n⟩
    let s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
    iterationSafe bestEntryRowStep BestEntryRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (fillBestEntryRowProg rowArgs)) ∧
      memoryCost (fillBestEntryRowProg rowArgs) s ≤ 5 * n ∧
      s1.frontier = s.frontier ∧
      (∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
        s1.mem addr = s.mem addr) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.1 * n + col.1) =
        if a[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.1 * n + col.1) =
        Signed.encode c[u.1][col.1]) ∧
      (∀ z : Fin n, s1.mem (frameMaskBase ws n k + z.1) = if inCycle[z.1] then 1 else 0) ∧
      (∀ z : Fin n,
        s1.mem (candPredBase ws n + z.1) = (if inCycle[z.1] && a[uFin.1][z.1] then 1 else 0) ∧
        s1.mem (candCostBase ws n + z.1) = Signed.encode c[uFin.1][z.1]) := by
  let rowArgs : BestEntryRowArgs :=
    ⟨n, uFin.1, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
      candPredBase ws n, candCostBase ws n⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := uFin.isLt
  have hfr_le := frame_le_frames hk
  have hrow := iterate_spec bestEntryRowStep BestEntryRowStepSafe w rowArgs 5 n
    (fun y idxR sr => idxR = y ∧ sr.frontier = s.frontier ∧
      (∀ u col : Fin n, sr.mem (curAdjBase ws n + u.1 * n + col.1) =
        if a[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n, sr.mem (curCostBase ws n + u.1 * n + col.1) =
        Signed.encode c[u.1][col.1]) ∧
      (∀ z : Fin n, sr.mem (frameMaskBase ws n k + z.1) = if inCycle[z.1] then 1 else 0) ∧
      (∀ z : Fin n, z.1 < y →
        sr.mem (candPredBase ws n + z.1) = (if inCycle[z.1] && a[uFin.1][z.1] then 1 else 0) ∧
        sr.mem (candCostBase ws n + z.1) = Signed.encode c[uFin.1][z.1]))
    (fun addr => candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n)
    (fun y hy idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hdone_r⟩ => by
      subst idxR
      have hcell_uy := List.mul_add_lt_sq hu_lt hy
      have hm_y : sr.mem (frameMaskBase ws n k + y) = if inCycle[y] then 1 else 0 := hm_r ⟨y, hy⟩
      have ha_my : sr.mem (curAdjBase ws n + uFin.1 * n + y) = if a[uFin.1][y] then 1 else 0 :=
        ha_r uFin ⟨y, hy⟩
      have hc_my : sr.mem (curCostBase ws n + uFin.1 * n + y) = Signed.encode c[uFin.1][y] :=
        hc_r uFin ⟨y, hy⟩
      refine ⟨by dsimp only [BestEntryRowStepSafe, rowArgs]; exact ⟨h1,
          hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, curAdjBase]; omega),
          hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
          hws.of_le (by dsimp only [wsSize, candPredBase]; omega),
          hws.of_le (by dsimp only [wsSize, candCostBase]; omega),
          hws.of_le (by dsimp only [wsSize]; omega)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold bestEntryRowStep
        dsimp only [rowArgs]
        exact validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega)
              (validHistory_write_bind
                (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega)
                (by split_ifs <;> first | exact h1 | exact fits_zero w)
                (validHistory_write_bind
                  (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega)
                  (hc_my ▸ hfit_c uFin ⟨y, hy⟩)
                  (validHistory_pure w _ _)))))
      · unfold bestEntryRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [bestEntryRowStep, rowArgs, client_simps]
      · intro addr haddr
        dsimp only [candPredBase, candCostBase] at haddr
        simp only [bestEntryRowStep, rowArgs, client_simps, candPredBase, candCostBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp [bestEntryRowStep, rowArgs, client_simps]
      · simpa [bestEntryRowStep, rowArgs, client_simps] using hfr_r
      · intro u col
        have := List.mul_add_lt_sq u.isLt col.isLt
        simp only [bestEntryRowStep, rowArgs, client_simps]
        rw [Function.update_of_ne (by dsimp only [curAdjBase, candCostBase]; omega),
          Function.update_of_ne (by dsimp only [curAdjBase, candPredBase]; omega)]
        exact ha_r u col
      · intro u col
        have := List.mul_add_lt_sq u.isLt col.isLt
        simp only [bestEntryRowStep, rowArgs, client_simps]
        rw [Function.update_of_ne (by dsimp only [curCostBase, candCostBase]; omega),
          Function.update_of_ne (by dsimp only [curCostBase, candPredBase]; omega)]
        exact hc_r u col
      · intro z
        have := z.isLt
        simp only [bestEntryRowStep, rowArgs, client_simps]
        rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, candCostBase]; omega),
          Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, candPredBase]; omega)]
        exact hm_r z
      · intro z hz
        simp only [bestEntryRowStep, rowArgs, client_simps]
        by_cases heq : z.1 = y
        · have hz_eq : z = ⟨y, hy⟩ := Fin.ext heq
          subst hz_eq
          simp only [Function.update_self]
          rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_self]
          simp only [hm_y, ha_my, hc_my]
          refine ⟨?_, trivial⟩
          cases inCycle[y] <;> cases a[uFin.1][y] <;> simp
        · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
          exact hdone_r z (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, ha_end, hc_end, hm_end, hdone_end⟩ := hrow
  unfold fillBestEntryRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, ha_end, hc_end, hm_end, fun z => hdone_end z z.isLt⟩

private theorem bestEntryProg_spec {w n ws k : ℕ} (hpos : 0 < n)
    (a : AdjTable n) (c : CostTable ℤ n) (inCycle : Vector Bool n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1])) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (bestEntryProg la)
    let bEntry := bestEntryTable a c inCycle
    iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w la n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (bestEntryProg la)) ∧
      memoryCost (bestEntryProg la) s₀ ≤ (7 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n)) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ u : Fin n, s'.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1]) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec bestEntryOuterStep BestEntryOuterStepSafe w la (7 * n + 2) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
          if a[u.1][col.1] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
          Signed.encode c[u.1][col.1]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ j : Fin n, j.1 < m →
          s.mem (frameBEntryBase ws n k + j.1) = optFinIdx (bestEntryTable a c inCycle)[j.1]))
    (fun addr => (candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n))
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      let rowArgs : BestEntryRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
          candPredBase ws n, candCostBase ws n⟩
      have hrow := fillBestEntryRowProg_spec uFin a c inCycle s hk hws (by rw [hfr]; exact hf)
        ha_s hc_s hm_s hfit_c
      set s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun y => inCycle[y.1] && a[m][y.1]) (fun y => c[m][y.1]) s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun y => (hrow.2.2.2.2.2.2.2.2 y).1)
        (fun y => (hrow.2.2.2.2.2.2.2.2 y).2)
      refine ⟨by dsimp only [BestEntryOuterStepSafe, la]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold bestEntryOuterStep
        dsimp only [la]
        have hfr_le := frame_le_frames hk
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_bind_step hrow.2.1 ?_
        refine validHistory_bind_step harg.2.1 ?_
        rw [harg.2.2.2.1]
        refine validHistory_write_bind
          (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf hfr ⊢;
              rw [hrow.2.2.2.1]; omega)
          ?_ (validHistory_pure w _ _)
        rw [harg.2.2.2.2]
        cases argMinFin n (fun y => inCycle[y.1] && a[m][y.1]) (fun y => c[m][y.1]) with
        | none => exact hws.of_le (by dsimp only [optFinIdx, wsSize]; omega)
        | some j => exact hws.of_le (by have := j.isLt; dsimp only [optFinIdx, wsSize]; omega)
      · unfold bestEntryOuterStep
        dsimp only [la]
        rw [memoryCost_bind', memoryCost_read, clientState_read,
          memoryCost_bind', memoryCost_bind', harg.2.2.2.1, memoryCost_bind', memoryCost_write]
        have hc_r : memoryCost (fillBestEntryRowProg rowArgs) s ≤ 5 * n := hrow.2.2.1
        have hc_a : memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
            2 * n := harg.2.2.1
        dsimp only [rowArgs, s1] at hc_r hc_a ⊢
        simp only [client_simps]
        omega
      · unfold bestEntryOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have hrow_fr := hrow.2.2.2.1
        dsimp only [s1, rowArgs, uFin] at harg_s hrow_fr
        simp [client_simps, harg_s, hrow_fr, hfr]
      · intro addr haddr
        have hne_be : addr ≠ frameBEntryBase ws n k + m :=
          fun heq => haddr (Or.inr ⟨by omega, by omega⟩)
        unfold bestEntryOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have hrow_mod := hrow.2.2.2.2.1
        dsimp only [s1, rowArgs, uFin] at harg_s hrow_mod
        simp only [client_simps, harg_s, Function.update_of_ne hne_be]
        exact hrow_mod addr (fun hc => haddr (Or.inl hc))
      · unfold bestEntryOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have harg_r := harg.2.2.2.2
        have hrow_fr := hrow.2.2.2.1
        have hrow_mod := hrow.2.2.2.2.1
        have hrow_a := hrow.2.2.2.2.2.1
        have hrow_c := hrow.2.2.2.2.2.2.1
        have hrow_m := hrow.2.2.2.2.2.2.2.1
        dsimp only [s1, rowArgs, uFin] at harg_s harg_r hrow_fr hrow_mod hrow_a hrow_c hrow_m
        simp only [client_simps, harg_s, harg_r]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_, ?_⟩
        · intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [Function.update_of_ne
            (by dsimp only [curAdjBase, frameBEntryBase, frameBase]; omega)]
          exact hrow_a u col
        · intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [Function.update_of_ne
            (by dsimp only [curCostBase, frameBEntryBase, frameBase]; omega)]
          exact hrow_c u col
        · intro y
          have := y.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBEntryBase, frameBase]; omega)]
          exact hrow_m y
        · intro j hj
          by_cases hjm : j.1 = m
          · have hju : j = uFin := Fin.ext hjm
            subst hju
            simp [bestEntryTable, uFin]
          · rw [Function.update_of_ne (by omega),
              hrow_mod _ (by
                dsimp only [candPredBase, candCostBase, frameBEntryBase, frameBase]; omega)]
            exact hdone_o j (by omega))
    0 s₀ ⟨rfl, rfl, ha, hc, hm, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, hdone_end⟩ := h
  unfold bestEntryProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun u => hdone_end u u.isLt⟩

private theorem fillBestExitRowProg_spec {w n ws k B_k : ℕ} (colFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (s : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hf_s : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let rowArgs : BestExitRowArgs :=
      ⟨n, colFin.1, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
        frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
    let exitVal : Fin n → ℤ := fun x =>
      if inCycle[x.1] && a[x.1][colFin.1] then c[x.1][colFin.1] - c[x.1][f[x.1].1] else 0
    let s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
    iterationSafe bestExitRowStep BestExitRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (fillBestExitRowProg rowArgs)) ∧
      memoryCost (fillBestExitRowProg rowArgs) s ≤ 7 * n ∧
      s1.frontier = s.frontier ∧
      (∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
        s1.mem addr = s.mem addr) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.1 * n + col.1) =
        if a[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.1 * n + col.1) =
        Signed.encode c[u.1][col.1]) ∧
      (∀ y : Fin n, s1.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
      (∀ z : Fin n, s1.mem (frameParentBase ws n k + z.1) = (f[z.1]).1) ∧
      (∀ z : Fin n,
        s1.mem (candPredBase ws n + z.1) = (if inCycle[z.1] && a[z.1][colFin.1] then 1 else 0) ∧
        s1.mem (candCostBase ws n + z.1) = Signed.encode (exitVal z)) := by
  let rowArgs : BestExitRowArgs :=
    ⟨n, colFin.1, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
      frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
  let exitVal : Fin n → ℤ := fun x =>
    if inCycle[x.1] && a[x.1][colFin.1] then c[x.1][colFin.1] - c[x.1][f[x.1].1] else 0
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hcol_lt := colFin.isLt
  have hfr_le := frame_le_frames hk
  have hrow := iterate_spec bestExitRowStep BestExitRowStepSafe w rowArgs 7 n
    (fun x idxR sr => idxR = x ∧ sr.frontier = s.frontier ∧
      (∀ u col : Fin n, sr.mem (curAdjBase ws n + u.1 * n + col.1) =
        if a[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n, sr.mem (curCostBase ws n + u.1 * n + col.1) =
        Signed.encode c[u.1][col.1]) ∧
      (∀ y : Fin n, sr.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
      (∀ z : Fin n, sr.mem (frameParentBase ws n k + z.1) = (f[z.1]).1) ∧
      (∀ z : Fin n, z.1 < x →
        sr.mem (candPredBase ws n + z.1) = (if inCycle[z.1] && a[z.1][colFin.1] then 1 else 0) ∧
        sr.mem (candCostBase ws n + z.1) = Signed.encode (exitVal z)))
    (fun addr => candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n)
    (fun x hx idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hf_r, hdone_r⟩ => by
      subst idxR
      set xFin : Fin n := ⟨x, hx⟩
      have hcell_xc := List.mul_add_lt_sq hx hcol_lt
      have hcell_xf := List.mul_add_lt_sq hx (f[x]).isLt
      have hm_x : sr.mem (frameMaskBase ws n k + x) = if inCycle[x] then 1 else 0 := hm_r xFin
      have ha_xm : sr.mem (curAdjBase ws n + x * n + colFin.1) = if a[x][colFin.1] then 1 else 0 :=
        ha_r xFin colFin
      have hc_xm : sr.mem (curCostBase ws n + x * n + colFin.1) = Signed.encode c[x][colFin.1] :=
        hc_r xFin colFin
      have hf_x : sr.mem (frameParentBase ws n k + x) = (f[x]).1 := hf_r xFin
      have hc_xf : sr.mem (curCostBase ws n + x * n + (f[x]).1) = Signed.encode c[x][f[x].1] :=
        hc_r xFin f[x]
      have h1b := hB xFin colFin
      have h2b := hB xFin f[x]
      have hcxf_fit1 : Fits w (sr.mem (curCostBase ws n + x * n +
          sr.mem (frameParentBase ws n k + x)) + 1) := by
        rw [hf_x, hc_xf]
        unfold Signed.encode
        exact hfit_diff.of_le (by split_ifs <;> linarith only [h2b])
      have hsub_fit : Fits w (2 * (sr.mem (curCostBase ws n + x * n + colFin.1) / 2 +
          sr.mem (curCostBase ws n + x * n + sr.mem (frameParentBase ws n k + x)) / 2) + 1) := by
        rw [hc_xm, hf_x, hc_xf, Signed.encode_div_two, Signed.encode_div_two]
        exact hfit_diff.of_le (by linarith only [h1b, h2b])
      refine ⟨by dsimp only [BestExitRowStepSafe, rowArgs]; exact ⟨h2,
          hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, curAdjBase]; omega),
          hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
          hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, candPredBase]; omega),
          hws.of_le (by dsimp only [wsSize, candCostBase]; omega),
          hws.of_le (by dsimp only [wsSize]; omega),
          fun _ => ⟨by rw [hf_x]; exact hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
            hcxf_fit1, hsub_fit⟩⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        refine validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr_r ⊢; omega) ?_)))
        split_ifs
        · refine validHistory_read_bind
            (by rw [hf_x]; dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega) ?_
          refine validHistory_bind_step (validHistory_signedSubProg w _ _) ?_
          rw [clientState_signedSubProg, hc_xm, hf_x, hc_xf, clientResult_signedSubProg]
          refine validHistory_write_bind
            (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega) h1
            (validHistory_write_bind
              (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega) ?_
              (validHistory_pure w _ _))
          have hdiff_abs : (c[x][colFin.1] - c[x][f[x].1]).natAbs ≤ 2 * B_k :=
            (Int.natAbs_sub_le _ _).trans (by linarith only [h1b, h2b])
          unfold Signed.encode
          exact hfit_diff.of_le (by split_ifs <;> linarith only [hdiff_abs])
        · exact validHistory_write_bind
            (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega) (fits_zero w)
            (validHistory_write_bind
              (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _))
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        split_ifs
        · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
            memoryCost_bind', memoryCost_signedSubProg, clientState_signedSubProg]
          simp only [memoryCost_bind', memoryCost_write, client_simps]
          omega
        · simp only [memoryCost_bind', memoryCost_write, client_simps]
          omega
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simp [client_simps]
      · intro addr haddr
        dsimp only [candPredBase, candCostBase] at haddr
        have hne1 : addr ≠ ws + 4 * (n * n) + n + x := by omega
        have hne2 : addr ≠ ws + 4 * (n * n) + x := by omega
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp [candPredBase, candCostBase, client_simps, Function.update_of_ne hne1,
          Function.update_of_ne hne2]
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simp [client_simps]
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simpa [client_simps] using hfr_r
      · intro u col
        have := List.mul_add_lt_sq u.isLt col.isLt
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        by_cases hcond_r : sr.mem (frameMaskBase ws n k + x) = 1 ∧
            sr.mem (curAdjBase ws n + x * n + colFin.1) = 1 <;>
          simp only [hcond_r, ↓reduceIte, client_simps]
        · rw [Function.update_of_ne (by dsimp only [curAdjBase, candCostBase]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, candPredBase]; omega)]
          exact ha_r u col
        · rw [Function.update_of_ne (by dsimp only [curAdjBase, candCostBase]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, candPredBase]; omega)]
          exact ha_r u col
      · intro u col
        have := List.mul_add_lt_sq u.isLt col.isLt
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        by_cases hcond_r : sr.mem (frameMaskBase ws n k + x) = 1 ∧
            sr.mem (curAdjBase ws n + x * n + colFin.1) = 1 <;>
          simp only [hcond_r, ↓reduceIte, client_simps]
        · rw [Function.update_of_ne (by dsimp only [curCostBase, candCostBase]; omega),
            Function.update_of_ne (by dsimp only [curCostBase, candPredBase]; omega)]
          exact hc_r u col
        · rw [Function.update_of_ne (by dsimp only [curCostBase, candCostBase]; omega),
            Function.update_of_ne (by dsimp only [curCostBase, candPredBase]; omega)]
          exact hc_r u col
      · intro y
        have := y.isLt
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        by_cases hcond_r : sr.mem (frameMaskBase ws n k + x) = 1 ∧
            sr.mem (curAdjBase ws n + x * n + colFin.1) = 1 <;>
          simp only [hcond_r, ↓reduceIte, client_simps]
        · rw [Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, candCostBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, candPredBase]; omega)]
          exact hm_r y
        · rw [Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, candCostBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, candPredBase]; omega)]
          exact hm_r y
      · intro z
        have := z.isLt
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        by_cases hcond_r : sr.mem (frameMaskBase ws n k + x) = 1 ∧
            sr.mem (curAdjBase ws n + x * n + colFin.1) = 1 <;>
          simp only [hcond_r, ↓reduceIte, client_simps]
        · rw [Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, candCostBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, candPredBase]; omega)]
          exact hf_r z
        · rw [Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, candCostBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, candPredBase]; omega)]
          exact hf_r z
      · intro z hz
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps, hm_x, ha_xm, hc_xm, hf_x]
        by_cases hcond : inCycle[x] = true ∧ a[x][colFin.1] = true
        · have hwcond : (if inCycle[x] = true then (1 : ℕ) else 0) = 1 ∧
              (if a[x][colFin.1] = true then (1 : ℕ) else 0) = 1 :=
            ⟨by simp [hcond.1], by simp [hcond.2]⟩
          simp only [hwcond, and_self, ↓reduceIte, hc_xf, clientResult_signedSubProg, client_simps]
          by_cases heq : z.1 = x
          · have hz_eq : z = xFin := Fin.ext heq
            subst hz_eq
            simp only [Function.update_self, exitVal, hcond.1, hcond.2, Bool.and_self,
              ↓reduceIte, xFin]
            rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_self]
            simp
          · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
            exact hdone_r z (by omega)
        · have hnwcond : ¬((if inCycle[x] = true then (1 : ℕ) else 0) = 1 ∧
              (if a[x][colFin.1] = true then (1 : ℕ) else 0) = 1) := by
            rintro ⟨h1w, h2w⟩
            apply hcond
            constructor
            · by_cases h1b : inCycle[x] = true
              · exact h1b
              · simp [h1b] at h1w
            · by_cases h2b : a[x][colFin.1] = true
              · exact h2b
              · simp [h2b] at h2w
          have hbcond : (inCycle[x] && a[x][colFin.1]) = false := by
            cases h1b : inCycle[x] <;> cases h2b : a[x][colFin.1] <;> simp_all
          simp only [hnwcond, ↓reduceIte, client_simps]
          by_cases heq : z.1 = x
          · have hz_eq : z = xFin := Fin.ext heq
            subst hz_eq
            simp only [Function.update_self, exitVal, hbcond, Bool.false_eq_true, ↓reduceIte,
              Signed.encode, lt_irrefl, Nat.add_zero, xFin]
            rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_self]
            exact ⟨rfl, rfl⟩
          · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
            exact hdone_r z (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, hf_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, ha_e, hc_e, hm_e, hf_e, hdone_e⟩ := hrow
  unfold fillBestExitRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, ha_e, hc_e, hm_e, hf_e, fun z => hdone_e z z.isLt⟩

private theorem bestExitProg_spec {w n ws k B_k : ℕ} (hpos : 0 < n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (s₀ : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.1 * n + col.1) =
      if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.1 * n + col.1) =
      Signed.encode c[u.1][col.1])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp : ∀ x : Fin n, s₀.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (bestExitProg la)
    let bExit := reducedBestExitTable a c f inCycle
    iterationSafe bestExitOuterStep BestExitOuterStepSafe w la n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (bestExitProg la)) ∧
      memoryCost (bestExitProg la) s₀ ≤ (9 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n)) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ col : Fin n, s'.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1]) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec bestExitOuterStep BestExitOuterStepSafe w la (9 * n + 2) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.1 * n + col.1) =
          if a[u.1][col.1] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.1 * n + col.1) =
          Signed.encode c[u.1][col.1]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1) ∧
        (∀ j : Fin n, j.1 < m →
          s.mem (frameBExitBase ws n k + j.1) =
            optFinIdx (reducedBestExitTable a c f inCycle)[j.1]))
    (fun addr => (candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n))
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hfp_s, hdone_o⟩ => by
      subst idx
      set colFin : Fin n := ⟨m, hm⟩
      let rowArgs : BestExitRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
          frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
      let exitVal : Fin n → ℤ := fun x =>
        if inCycle[x.1] && a[x.1][m] then c[x.1][m] - c[x.1][f[x.1].1] else 0
      have hrow := fillBestExitRowProg_spec colFin a c f inCycle s hk hws
        (by rw [hfr]; exact hf) hfit_diff ha_s hc_s hm_s hfp_s hB
      set s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun x => inCycle[x.1] && a[x.1][m]) exitVal s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun x => (hrow.2.2.2.2.2.2.2.2.2 x).1)
        (fun x => (hrow.2.2.2.2.2.2.2.2.2 x).2)
      have hargmin_eq : argMinFin n (fun x => inCycle[x.1] && a[x.1][m]) exitVal =
          (reducedBestExitTable a c f inCycle)[m] := by
        simp only [reducedBestExitTable, Vector.getElem_ofFn]
        exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
          simp only [Bool.and_eq_true] at hx hy
          simp [exitVal, hx.1, hx.2, hy.1, hy.2]
      refine ⟨by dsimp only [BestExitOuterStepSafe, la]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold bestExitOuterStep
        dsimp only [la]
        have hfr_le := frame_le_frames hk
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_bind_step hrow.2.1 ?_
        refine validHistory_bind_step harg.2.1 ?_
        rw [harg.2.2.2.1]
        refine validHistory_write_bind
          (by dsimp only [wsSize, frameBExitBase, frameBase] at hf hfr ⊢;
              rw [hrow.2.2.2.1]; omega)
          ?_ (validHistory_pure w _ _)
        rw [harg.2.2.2.2]
        cases argMinFin n (fun x => inCycle[x.1] && a[x.1][m]) exitVal with
        | none => exact hws.of_le (by dsimp only [optFinIdx, wsSize]; omega)
        | some j => exact hws.of_le (by have := j.isLt; dsimp only [optFinIdx, wsSize]; omega)
      · unfold bestExitOuterStep
        dsimp only [la]
        rw [memoryCost_bind', memoryCost_read, clientState_read,
          memoryCost_bind', memoryCost_bind', harg.2.2.2.1, memoryCost_bind', memoryCost_write]
        have hc_r : memoryCost (fillBestExitRowProg rowArgs) s ≤ 7 * n := hrow.2.2.1
        have hc_a : memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
            2 * n := harg.2.2.1
        dsimp only [rowArgs, s1] at hc_r hc_a ⊢
        simp only [client_simps]
        omega
      · unfold bestExitOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have hrow_fr := hrow.2.2.2.1
        dsimp only [s1, rowArgs, colFin] at harg_s hrow_fr
        simp [client_simps, harg_s, hrow_fr, hfr]
      · intro addr haddr
        have hne_bx : addr ≠ frameBExitBase ws n k + m :=
          fun heq => haddr (Or.inr ⟨by omega, by omega⟩)
        unfold bestExitOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have hrow_mod := hrow.2.2.2.2.1
        dsimp only [s1, rowArgs, colFin] at harg_s hrow_mod
        simp only [client_simps, harg_s, Function.update_of_ne hne_bx]
        exact hrow_mod addr (fun hc => haddr (Or.inl hc))
      · unfold bestExitOuterStep
        dsimp only [la]
        have harg_s := harg.2.2.2.1
        have harg_r := harg.2.2.2.2
        have hrow_fr := hrow.2.2.2.1
        have hrow_mod := hrow.2.2.2.2.1
        have hrow_a := hrow.2.2.2.2.2.1
        have hrow_c := hrow.2.2.2.2.2.2.1
        have hrow_m := hrow.2.2.2.2.2.2.2.1
        have hrow_f := hrow.2.2.2.2.2.2.2.2.1
        dsimp only [s1, rowArgs, colFin] at harg_s harg_r hrow_fr hrow_mod hrow_a hrow_c
        dsimp only [s1, rowArgs, colFin] at hrow_m hrow_f
        simp only [client_simps, harg_s, harg_r, hargmin_eq]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_, ?_, ?_⟩
        · intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [Function.update_of_ne
            (by dsimp only [curAdjBase, frameBExitBase, frameBase]; omega)]
          exact hrow_a u col
        · intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [Function.update_of_ne
            (by dsimp only [curCostBase, frameBExitBase, frameBase]; omega)]
          exact hrow_c u col
        · intro y
          have := y.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBExitBase, frameBase]; omega)]
          exact hrow_m y
        · intro x
          have := x.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameParentBase, frameBExitBase, frameBase]; omega)]
          exact hrow_f x
        · intro j hj
          by_cases hjm : j.1 = m
          · simp [hjm]
          · rw [Function.update_of_ne (by omega),
              hrow_mod _ (by
                dsimp only [candPredBase, candCostBase, frameBExitBase, frameBase]; omega)]
            exact hdone_o j (by omega))
    0 s₀ ⟨rfl, rfl, ha, hc, hm, hfp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, hdone_end⟩ := h
  unfold bestExitProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

private theorem contractReducedCostTable_natAbs_le {n B_k : ℕ} (a : AdjTable n) (c : CostTable ℤ n)
    (f : ParentTable n) (inCycle : Vector Bool n) (bEntry bExit : Vector (Option (Fin n)) n)
    (x0 : Fin n) (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) (u col : Fin n) :
    ((contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]).natAbs ≤ 2 * B_k := by
  rw [getElem_contractReducedCostTable]
  split_ifs
  · cases bExit[col.1] with
    | none => simp
    | some xs => exact (Int.natAbs_sub_le _ _).trans (by linarith only [hB xs col, hB xs f[xs.1]])
  · simp
  · simp
  · cases bEntry[u.1] with
    | none => simp
    | some ys => exact (hB u ys).trans (by omega)
  · simp
  · exact (hB u col).trans (by omega)
  · simp

private theorem contractCostCellProg_eval {w n ws k B_k : ℕ} (r x0 u col : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ x y : Fin n,
      s.mem (curAdjBase ws n + x.1 * n + y.1) = if a[x.1][y.1] then 1 else 0)
    (hc : ∀ x y : Fin n, s.mem (curCostBase ws n + x.1 * n + y.1) = Signed.encode c[x.1][y.1])
    (hm : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe : ∀ x : Fin n, s.mem (frameBEntryBase ws n k + x.1) = optFinIdx bEntry[x.1])
    (hbx : ∀ y : Fin n, s.mem (frameBExitBase ws n k + y.1) = optFinIdx bExit[y.1])
    (hB : ∀ x y : Fin n, (c[x.1][y.1]).natAbs ≤ B_k) :
    let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    ContractRowStepSafe w q s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (contractCostCellProg q)) ∧
      memoryCost (contractCostCellProg q) s ≤ 10 ∧
      (Memory.spec 0).clientState s (contractCostCellProg q) =
        ⟨Function.update s.mem (nextCostBase ws n + u.1 * n + col.1)
          (Signed.encode c'[u.1][col.1]), s.frontier⟩ := by
  let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
  have hu_lt := u.isLt
  have hc_lt := col.isLt
  have hcell_uc := List.mul_add_lt_sq hu_lt hc_lt
  have hfr_le := frame_le_frames hk
  have hm_u := hm u
  have hm_c := hm col
  have ha_uc := ha u col
  have hc_uc := hc u col
  have hbe_u := hbe u
  have hbx_c := hbx col
  have hfit_c' : Fits w (Signed.encode
      (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]) := by
    have habs := contractReducedCostTable_natAbs_le a c f inCycle bEntry bExit x0 hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [habs])
  have hsafe : ContractRowStepSafe w q s := by
    dsimp only [ContractRowStepSafe, q]
    refine ⟨hu_lt, hc_lt, hk, hws, fun _ _ _ hbx_lt => ?_⟩
    rw [hbx_c] at hbx_lt ⊢
    cases hb_case : bExit[col.1] with
    | none => simp [hb_case, optFinIdx] at hbx_lt
    | some xs =>
      simp only [optFinIdx]
      rw [hfp xs, hc xs col, hc xs f[xs.1], Signed.encode_div_two, Signed.encode_div_two]
      have h1b := hB xs col
      have h2b := hB xs f[xs.1]
      refine ⟨(f[xs.1]).isLt, ?_, hfit_diff.of_le (by linarith only [h1b, h2b])⟩
      unfold Signed.encode
      exact hfit_diff.of_le (by split_ifs <;> linarith only [h2b])
  refine ⟨hsafe, ?_, ?_, ?_⟩
  · unfold contractCostCellProg
    dsimp only [q]
    refine validHistory_read_bind
      (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
      (validHistory_read_bind
        (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
        (validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curCostBase] at hf ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢; omega) ?_)))))
    rw [hm_u, hm_c, ha_uc, hc_uc, hbe_u, hbx_c]
    by_cases huC : inCycle[u.1] = true
    · simp only [huC, ↓reduceIte]
      by_cases hux : u = x0
      · subst hux
        simp only [↓reduceIte]
        by_cases hwC : inCycle[col.1] = true
        · simp only [hwC, ↓reduceIte, Nat.one_ne_zero, false_and]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
        · simp only [hwC, Bool.false_eq_true, ↓reduceIte, true_and]
          cases hb_case : bExit[col.1] with
          | none =>
            simp only [optFinIdx, lt_irrefl, ↓reduceIte]
            exact validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _)
          | some xs =>
            have hcell_xc := List.mul_add_lt_sq xs.isLt hc_lt
            have hcell_xf := List.mul_add_lt_sq xs.isLt (f[xs.1]).isLt
            have hxs_lt := xs.isLt
            simp only [optFinIdx, hxs_lt, ↓reduceIte]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameParentBase, frameBase] at hf ⊢; omega) ?_)
            rw [hfp xs]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega) ?_
            refine validHistory_bind_step (validHistory_signedSubProg w _ _) ?_
            rw [clientState_signedSubProg, hc xs col, hc xs f[xs.1], clientResult_signedSubProg]
            refine validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
              (validHistory_pure w _ _)
            simpa [getElem_contractReducedCostTable, huC, hwC, hb_case] using hfit_c'
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        simp only [hux_v, ↓reduceIte]
        exact validHistory_write_bind
          (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
          (validHistory_pure w _ _)
    · simp only [huC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
      by_cases hwC : inCycle[col.1] = true
      · simp only [hwC, ↓reduceIte]
        by_cases hcx : col = x0
        · subst hcx
          simp only [true_and]
          cases hbe_case : bEntry[u.1] with
          | none =>
            simp only [optFinIdx, lt_irrefl, ↓reduceIte]
            exact validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _)
          | some ys =>
            have hcell_uy := List.mul_add_lt_sq hu_lt ys.isLt
            simp only [optFinIdx, ys.isLt, ↓reduceIte]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega) ?_
            rw [hc u ys]
            refine validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
              (validHistory_pure w _ _)
            simpa [getElem_contractReducedCostTable, huC, hwC, hbe_case] using hfit_c'
        · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
          simp only [hcx_v, false_and, ↓reduceIte]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
      · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        by_cases ha_b : a[u.1][col.1] = true
        · simp only [ha_b, ↓reduceIte]
          refine validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
            (validHistory_pure w _ _)
          simpa [getElem_contractReducedCostTable, huC, hwC, ha_b] using hfit_c'
        · simp only [ha_b, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
  · unfold contractCostCellProg
    dsimp only [q]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
    split_ifs
    · simp only [memoryCost_bind', memoryCost_read, clientResult_read,
        memoryCost_signedSubProg, memoryCost_write, client_simps]
      omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_read, memoryCost_write, client_simps]
      omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
  · unfold contractCostCellProg
    dsimp only [q]
    simp only [client_simps, hm_u, hm_c, ha_uc, hc_uc, hbe_u, hbx_c]
    rw [getElem_contractReducedCostTable]
    by_cases huC : inCycle[u.1] = true
    · simp only [huC, ↓reduceIte]
      by_cases hux : u = x0
      · subst hux
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases hwC : inCycle[col.1] = true
        · simp [hwC, Signed.encode, client_simps]
        · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Bool.not_false, true_and]
          cases hb_case : bExit[col.1] with
          | none => simp [optFinIdx, Signed.encode, client_simps]
          | some xs =>
            simp [optFinIdx, xs.isLt, hc xs col, hfp xs, hc xs f[xs.1],
              clientResult_signedSubProg, client_simps]
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        have hux_b : (u == x0) = false := beq_false_of_ne hux
        simp [hux_v, hux_b, Signed.encode, client_simps]
    · simp only [huC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
      by_cases hwC : inCycle[col.1] = true
      · simp only [hwC, ↓reduceIte]
        by_cases hcx : col = x0
        · subst hcx
          simp only [beq_self_eq_true, ↓reduceIte, true_and]
          cases hbe_case : bEntry[u.1] with
          | none => simp [optFinIdx, Signed.encode, client_simps]
          | some ys => simp [optFinIdx, ys.isLt, hc u ys, client_simps]
        · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
          have hcx_b : (col == x0) = false := beq_false_of_ne hcx
          simp [hcx_v, hcx_b, Signed.encode, client_simps]
      · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        by_cases ha_b : a[u.1][col.1] = true
        · simp [ha_b, client_simps]
        · simp [ha_b, Signed.encode, client_simps]

private theorem contractAdjCellProg_eval {w n ws k : ℕ} (r x0 u col : Fin n)
    (a : AdjTable n) (inCycle : Vector Bool n) (bEntry bExit : Vector (Option (Fin n)) n)
    (s : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha : ∀ x y : Fin n,
      s.mem (curAdjBase ws n + x.1 * n + y.1) = if a[x.1][y.1] then 1 else 0)
    (hm : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hbe : ∀ x : Fin n, s.mem (frameBEntryBase ws n k + x.1) = optFinIdx bEntry[x.1])
    (hbx : ∀ y : Fin n, s.mem (frameBExitBase ws n k + y.1) = optFinIdx bExit[y.1]) :
    let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (contractAdjCellProg q)) ∧
      memoryCost (contractAdjCellProg q) s ≤ 6 ∧
      (Memory.spec 0).clientState s (contractAdjCellProg q) =
        ⟨Function.update s.mem (nextAdjBase ws n + u.1 * n + col.1)
          (if a'[u.1][col.1] then 1 else 0), s.frontier⟩ := by
  let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := u.isLt
  have hc_lt := col.isLt
  have hcell_uc := List.mul_add_lt_sq hu_lt hc_lt
  have hfr_le := frame_le_frames hk
  have hm_u := hm u
  have hm_c := hm col
  have ha_uc := ha u col
  have hbe_u := hbe u
  have hbx_c := hbx col
  refine ⟨?_, ?_, ?_⟩
  · unfold contractAdjCellProg
    dsimp only [q]
    refine validHistory_read_bind
      (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
      (validHistory_read_bind
        (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
        (validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢; omega) ?_))))
    refine validHistory_write_bind
      (by dsimp only [wsSize, nextAdjBase] at hf ⊢; omega) ?_
      (validHistory_pure w _ _)
    rw [ha_uc]
    split_ifs <;> first | exact h1 | exact fits_zero w
  · unfold contractAdjCellProg
    dsimp only [q]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_write]
  · unfold contractAdjCellProg
    dsimp only [q]
    simp only [client_simps, hm_u, hm_c, ha_uc, hbe_u, hbx_c, getElem_contractAdjTable]
    apply congrArg (fun v =>
      (⟨Function.update s.mem (nextAdjBase ws n + u.1 * n + col.1) v, s.frontier⟩ : Memory.State))
    cases hu_b : inCycle[u.1] <;> cases hc_b : inCycle[col.1]
    · cases a[u.1][col.1] <;> simp
    · by_cases hcx : col = x0
      · subst hcx
        cases bEntry[u.1] with
        | none => simp [optFinIdx]
        | some ys => simp [optFinIdx, ys.isLt]
      · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
        simp [hcx, hcx_v]
    · by_cases hux : u = x0
      · subst hux
        cases bExit[col.1] with
        | none => simp [optFinIdx]
        | some xs => simp [optFinIdx, xs.isLt]
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        by_cases hcr : col = r
        · subst hcr; simp [hux, hux_v]
        · have hcr_v : col.1 ≠ r.1 := fun h => hcr (Fin.ext h)
          simp [hux, hux_v, hcr, hcr_v]
    · by_cases hux : u = x0
      · subst hux; simp
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        by_cases hcr : col = r
        · subst hcr; simp [hux, hux_v]
        · have hcr_v : col.1 ≠ r.1 := fun h => hcr (Fin.ext h)
          simp [hux, hux_v, hcr, hcr_v]

private theorem fillContractRowProg_spec {w n ws k B_k : ℕ} (r x0 uFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha_s : ∀ u col : Fin n,
      s.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc_s : ∀ u col : Fin n,
      s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp_s : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe_s : ∀ u : Fin n, s.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1])
    (hbx_s : ∀ col : Fin n, s.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1])
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ra : ContractRowArgs := ⟨n, r.1, x0.1, uFin.1, ws, k⟩
    let sr' := (Memory.spec 0).clientState s (fillContractRowProg ra)
    iterationSafe contractRowStep ContractRowStepSafe w ra n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillContractRowProg ra)) ∧
      memoryCost (fillContractRowProg ra) s ≤ 16 * n ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(nextAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < nextAdjBase ws n + uFin.1 * n + n ∨
        nextCostBase ws n + uFin.1 * n ≤ addr ∧ addr < nextCostBase ws n + uFin.1 * n + n) →
        sr'.mem addr = s.mem addr) ∧
      (∀ col : Fin n,
        sr'.mem (nextAdjBase ws n + uFin.1 * n + col.1) =
          (if (contractAdjTable a inCycle bEntry bExit x0 r)[uFin.1][col.1] then 1 else 0) ∧
        sr'.mem (nextCostBase ws n + uFin.1 * n + col.1) =
          Signed.encode
            (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][col.1]) := by
  let ra : ContractRowArgs := ⟨n, r.1, x0.1, uFin.1, ws, k⟩
  have hrow := iterate_spec contractRowStep ContractRowStepSafe w ra 16 n
    (fun col idxR sr =>
      idxR = col ∧ sr.frontier = s.frontier ∧
        (∀ u c0 : Fin n,
          sr.mem (curAdjBase ws n + u.1 * n + c0.1) = if a[u.1][c0.1] then 1 else 0) ∧
        (∀ u c0 : Fin n,
          sr.mem (curCostBase ws n + u.1 * n + c0.1) = Signed.encode c[u.1][c0.1]) ∧
        (∀ y : Fin n, sr.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ x : Fin n, sr.mem (frameParentBase ws n k + x.1) = (f[x.1]).1) ∧
        (∀ u : Fin n, sr.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1]) ∧
        (∀ c0 : Fin n, sr.mem (frameBExitBase ws n k + c0.1) = optFinIdx bExit[c0.1]) ∧
        (∀ c0 : Fin n, c0.1 < col →
          sr.mem (nextAdjBase ws n + uFin.1 * n + c0.1) =
            (if (contractAdjTable a inCycle bEntry bExit x0 r)[uFin.1][c0.1] then 1 else 0) ∧
          sr.mem (nextCostBase ws n + uFin.1 * n + c0.1) =
            Signed.encode
              (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][c0.1]))
    (fun addr => nextAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < nextAdjBase ws n + uFin.1 * n + n ∨
      nextCostBase ws n + uFin.1 * n ≤ addr ∧ addr < nextCostBase ws n + uFin.1 * n + n)
    (fun col hcol idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hfp_r, hbe_r, hbx_r, hcur⟩ => by
      subst idxR
      set colFin : Fin n := ⟨col, hcol⟩
      have hu_lt := uFin.isLt
      have hcell_uc := List.mul_add_lt_sq hu_lt hcol
      have hcost_ev := contractCostCellProg_eval r x0 uFin colFin a c f inCycle bEntry bExit
        sr hk hws (by rw [hfr_r]; exact hf) hfit_diff ha_r hc_r hm_r hfp_r hbe_r hbx_r hB
      set sr1 : Memory.State :=
        ⟨Function.update sr.mem (nextCostBase ws n + uFin.1 * n + col)
          (Signed.encode (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][col]),
          sr.frontier⟩
      have hadj_ev := contractAdjCellProg_eval r x0 uFin colFin a inCycle bEntry bExit
        sr1 hk hws (by dsimp only [sr1]; rw [hfr_r]; exact hf)
        (fun x y => by
          have := List.mul_add_lt_sq x.isLt y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne (by dsimp only [curAdjBase, nextCostBase]; omega)]
          exact ha_r x y)
        (fun y => by
          have := y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)]
          exact hm_r y)
        (fun x => by
          have := x.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)]
          exact hbe_r x)
        (fun y => by
          have := y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)]
          exact hbx_r y)
      have hcost_s := hcost_ev.2.2.2
      have hadj_s := hadj_ev.2.2
      dsimp only [ra, colFin] at hcost_s hadj_s
      refine ⟨hcost_ev.1, ?_, ?_, ?_, ?_, ?_⟩
      · unfold contractRowStep
        refine validHistory_bind_step hcost_ev.2.1 ?_
        rw [hcost_s]
        exact validHistory_bind_step hadj_ev.1 (validHistory_pure w _ _)
      · unfold contractRowStep
        rw [memoryCost_bind', hcost_s, memoryCost_bind']
        have h1c := hcost_ev.2.2.1
        have h2c := hadj_ev.2.1
        dsimp only [ra, colFin, sr1] at h1c h2c ⊢
        simp only [client_simps]
        omega
      · unfold contractRowStep
        dsimp only [ra, colFin]
        dsimp only [sr1] at hadj_s
        simp only [client_simps, hcost_s, hadj_s]
      · intro addr haddr
        unfold contractRowStep
        dsimp only [ra, colFin]
        simp only [client_simps, hcost_s, hadj_s, sr1]
        dsimp only [nextAdjBase, nextCostBase] at haddr ⊢
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · unfold contractRowStep
        dsimp only [ra, colFin]
        simp only [client_simps, hcost_s, hadj_s, sr1]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [Function.update_of_ne (by dsimp only [curAdjBase, nextAdjBase]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, nextCostBase]; omega)]
          exact ha_r u0 c0
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase, nextAdjBase]; omega),
            Function.update_of_ne (by dsimp only [curCostBase, nextCostBase]; omega)]
          exact hc_r u0 c0
        · intro y
          have := y.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)]
          exact hm_r y
        · intro x
          have := x.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, nextCostBase]; omega)]
          exact hfp_r x
        · intro u0
          have := u0.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameBEntryBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)]
          exact hbe_r u0
        · intro c0
          have := c0.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameBExitBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)]
          exact hbx_r c0
        · intro c0 hc0
          by_cases heq : c0.1 = col
          · have hc0_eq : c0 = colFin := Fin.ext heq
            subst hc0_eq
            simp only [Function.update_self, colFin]
            rw [Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_self]
            simp
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_of_ne (by omega)]
            exact hcur c0 (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, hfp_s, hbe_s, hbx_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, _, _, hdone_end⟩ := hrow
  unfold fillContractRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

private theorem contractTablesProg_spec {w n ws k B_k : ℕ} (r x0 : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp : ∀ x : Fin n, s₀.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe : ∀ u : Fin n, s₀.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1])
    (hbx : ∀ col : Fin n, s₀.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1])
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
    let s1 := (Memory.spec 0).clientState s₀ (contractLoopProg ca)
    let cp : CopyArgs := ⟨nextAdjBase ws n, curAdjBase ws n, 2 * (n * n)⟩
    let s' := (Memory.spec 0).clientState s₀ (contractTablesProg ca)
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    (iterationSafe contractOuterStep ContractOuterStepSafe w ca n 0 s₀ ∧
      iterationSafe copyStep CopyStepSafe w cp (2 * (n * n)) 0 s1) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (contractTablesProg ca)) ∧
      memoryCost (contractTablesProg ca) s₀ ≤ (16 * n + 1) * n + 4 * (n * n) ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + 4 * (n * n)) → s'.mem addr = s₀.mem addr) ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if a'[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c'[u.1][col.1]) := by
  let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
  have hf_pos : 0 < s₀.frontier := by have := r.pos; dsimp only [wsSize] at hf; nlinarith
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfit_c' : ∀ u col : Fin n,
      Fits w (Signed.encode
        (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]) := by
    intro u col
    have habs := contractReducedCostTable_natAbs_le a c f inCycle bEntry bExit x0 hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [habs])
  have hloop := iterate_spec contractOuterStep ContractOuterStepSafe w ca (16 * n + 1) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n,
          s.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0) ∧
        (∀ u col : Fin n,
          s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1) ∧
        (∀ u : Fin n, s.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1]) ∧
        (∀ col : Fin n, s.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1]) ∧
        (∀ u col : Fin n, u.1 < m →
          s.mem (nextAdjBase ws n + u.1 * n + col.1) =
            (if (contractAdjTable a inCycle bEntry bExit x0 r)[u.1][col.1] then 1 else 0) ∧
          s.mem (nextCostBase ws n + u.1 * n + col.1) =
            Signed.encode
              (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]))
    (fun addr => nextAdjBase ws n ≤ addr ∧ addr < nextCostBase ws n + n * n)
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hfp_s, hbe_s, hbx_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      let ra : ContractRowArgs := ⟨n, r.1, x0.1, m, ws, k⟩
      have hrow := fillContractRowProg_spec r x0 uFin a c f inCycle bEntry bExit s
        hk hws (by rw [hfr]; exact hf) hfit_diff ha_s hc_s hm_s hfp_s hbe_s hbx_s hB
      have hdisj_row : ∀ addr, addr < nextAdjBase ws n + m * n ∨
          nextAdjBase ws n + m * n + n ≤ addr ∧ addr < nextCostBase ws n + m * n ∨
          nextCostBase ws n + m * n + n ≤ addr →
          ((Memory.spec 0).clientState s (fillContractRowProg ra)).mem addr = s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, nextAdjBase, nextCostBase] at h ⊢; omega)
      have hm_mul : m * n + n ≤ n * n := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hm
      refine ⟨by dsimp only [ContractOuterStepSafe, ca]; exact ⟨hws.of_le
          (by dsimp only [wsSize]; omega), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold contractOuterStep
        dsimp only [ca]
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold contractOuterStep
        dsimp only [ca]
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillContractRowProg ra) s ≤ 16 * n := hrow.2.2.1
        dsimp only [ra] at hc_r ⊢
        simp only [client_simps]
        omega
      · unfold contractOuterStep
        dsimp only [ca]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold contractOuterStep
        dsimp only [ca]
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, nextAdjBase, nextCostBase] at haddr ⊢; omega)
      · unfold contractOuterStep
        dsimp only [ca]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [hdisj_row _ (Or.inl (by dsimp only [curAdjBase, nextAdjBase]; omega))]
          exact ha_s u0 c0
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [hdisj_row _ (Or.inl (by dsimp only [curCostBase, nextAdjBase]; omega))]
          exact hc_s u0 c0
        · intro y
          have := y.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)))]
          exact hm_s y
        · intro x
          have := x.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameParentBase, frameBase, nextCostBase]; omega)))]
          exact hfp_s x
        · intro u0
          have := u0.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)))]
          exact hbe_s u0
        · intro c0
          have := c0.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)))]
          exact hbx_s c0
        · intro u0 c0 hu0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu0) with hlt | heq
          · have hlt_mul : u0.1 * n + c0.1 < m * n := by
              have hc_lt := c0.isLt
              have hu_le : (u0.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n hlt
              linarith [Nat.succ_mul u0.1 n]
            rw [hdisj_row _ (Or.inl (by dsimp only [nextAdjBase]; omega)),
              hdisj_row _ (Or.inr (Or.inl (by dsimp only [nextAdjBase, nextCostBase]; omega)))]
            exact hdone_o u0 c0 hlt
          · have hu_eq : u0 = uFin := Fin.ext heq
            subst hu_eq
            exact hrow.2.2.2.2.2 c0)
    0 s₀ ⟨rfl, rfl, ha, hc, hm, hfp, hbe, hbx, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe_l, hvh_l, hmc_l, hs1_fr, hmod_l, _, _, _, _, _, _, _, _, hs1_cells⟩ := hloop
  set s1 := (Memory.spec 0).clientState s₀ (contractLoopProg ca)
  have hs1_fr' : s1.frontier = s₀.frontier := hs1_fr
  let cp : CopyArgs := ⟨nextAdjBase ws n, curAdjBase ws n, 2 * (n * n)⟩
  have hcopy := copyWordsProg_spec cp s1
    (by dsimp only [cp, wsSize, nextAdjBase] at hf ⊢; rw [hs1_fr']; omega)
    (by dsimp only [cp, wsSize, curAdjBase] at hf ⊢; rw [hs1_fr']; omega)
    (Or.inr (by dsimp only [cp, curAdjBase, nextAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize, nextAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize, curAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize]; omega))
    (fun i hi => by
      dsimp only [cp] at hi ⊢
      by_cases hlt : i < n * n
      · set u0 : Fin n := ⟨i / n, Nat.div_lt_of_lt_mul hlt⟩
        set c0 : Fin n := ⟨i % n, Nat.mod_lt i r.pos⟩
        rw [show nextAdjBase ws n + i = nextAdjBase ws n + u0.1 * n + c0.1 by
          have := Nat.div_add_mod' i n; dsimp only [u0, c0]; omega]
        dsimp only [s1, contractLoopProg]
        rw [(hs1_cells u0 c0 u0.isLt).1]
        split_ifs <;> first | exact h1 | exact fits_zero w
      · set j := i - n * n
        have hj : j < n * n := by omega
        set u0 : Fin n := ⟨j / n, Nat.div_lt_of_lt_mul hj⟩
        set c0 : Fin n := ⟨j % n, Nat.mod_lt j r.pos⟩
        rw [show nextAdjBase ws n + i = nextCostBase ws n + u0.1 * n + c0.1 by
          have hdm : (j / n) * n + j % n = j := Nat.div_add_mod' j n
          dsimp only [u0, c0, nextAdjBase, nextCostBase]
          omega]
        dsimp only [s1, contractLoopProg]
        rw [(hs1_cells u0 c0 u0.isLt).2]
        exact hfit_c' u0 c0)
  unfold contractTablesProg
  refine ⟨⟨hsafe_l, hcopy.1⟩, validHistory_bind_step hvh_l hcopy.2.1,
    by
      rw [memoryCost_bind']
      have hl_c : memoryCost (contractLoopProg ca) s₀ ≤ (16 * n + 1) * n := hmc_l
      have hcp_c := hcopy.2.2.1
      dsimp only [ca, cp] at hl_c hcp_c ⊢
      nlinarith only [hl_c, hcp_c],
    by
      rw [StateTransitionSpec.clientState_bind]
      exact hcopy.2.2.2.1.trans hs1_fr',
    fun addr haddr => by
      rw [StateTransitionSpec.clientState_bind]
      rw [hcopy.2.2.2.2.1 addr (by dsimp only [cp, curAdjBase]; omega)]
      exact hmod_l addr (by dsimp only [nextAdjBase, nextCostBase]; omega),
    fun u col => by
      rw [StateTransitionSpec.clientState_bind]
      have hidx_lt : u.1 * n + col.1 < 2 * (n * n) := by
        have := List.mul_add_lt_sq u.isLt col.isLt; omega
      rw [show curAdjBase ws n + u.1 * n + col.1 = cp.dst + (u.1 * n + col.1) by
          dsimp only [cp, curAdjBase]; omega,
        hcopy.2.2.2.2.2 _ hidx_lt,
        show cp.src + (u.1 * n + col.1) = nextAdjBase ws n + u.1 * n + col.1 by
          dsimp only [cp, nextAdjBase]; omega]
      exact (hs1_cells u col u.isLt).1,
    fun u col => by
      rw [StateTransitionSpec.clientState_bind]
      have hidx_lt : n * n + (u.1 * n + col.1) < 2 * (n * n) := by
        have := List.mul_add_lt_sq u.isLt col.isLt; omega
      rw [show curCostBase ws n + u.1 * n + col.1 = cp.dst + (n * n + (u.1 * n + col.1)) by
          dsimp only [cp, curAdjBase, curCostBase]; omega,
        hcopy.2.2.2.2.2 _ hidx_lt,
        show cp.src + (n * n + (u.1 * n + col.1)) = nextCostBase ws n + u.1 * n + col.1 by
          dsimp only [cp, nextAdjBase, nextCostBase]; omega]
      exact (hs1_cells u col u.isLt).2⟩

private theorem fillExpandRowProg_spec {w n ws k : ℕ} (x0 : Fin n)
    (f q : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q[v.1]).1)
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hm : ∀ v : Fin n, s₀.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0)
    (hbe : ∀ v : Fin n, s₀.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1]) :
    let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
    let s1 := (Memory.spec 0).clientState s₀ (fillExpandRowProg ra)
    iterationSafe expandRowStep ExpandRowStepSafe w ra n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (fillExpandRowProg ra)) ∧
      memoryCost (fillExpandRowProg ra) s₀ ≤ 5 * n ∧
      s1.frontier = s₀.frontier ∧
      (∀ addr, ¬(nextParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s1.mem addr = s₀.mem addr) ∧
      (∀ j : Fin n,
        s1.mem (nextParentBase ws n + j.1) =
          ((expandParentTable f inCycle bEntry bExit x0 q)[j.1]).1) := by
  let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
  have hrow := iterate_spec expandRowStep ExpandRowStepSafe w ra 5 n
    (fun m idx sr =>
      idx = m ∧ sr.frontier = s₀.frontier ∧
        (∀ v : Fin n, sr.mem (curParentBase ws n + v.1) = (q[v.1]).1) ∧
        (∀ v : Fin n, sr.mem (frameParentBase ws n k + v.1) = (f[v.1]).1) ∧
        (∀ v : Fin n, sr.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0) ∧
        (∀ v : Fin n, sr.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1]) ∧
        (∀ j : Fin n, j.1 < m → sr.mem (nextParentBase ws n + j.1) =
          ((expandParentTable f inCycle bEntry bExit x0 q)[j.1]).1))
    (fun addr => nextParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n)
    (fun m hm idx sr ⟨hidx, hfr_r, hcur_r, hfp_r, hm_r, hbe_r, hdone_r⟩ => by
      subst idx
      have hm_m : sr.mem (frameMaskBase ws n k + m) = if inCycle[m] then 1 else 0 := hm_r ⟨m, hm⟩
      have hfp_m : sr.mem (frameParentBase ws n k + m) = (f[m]).1 := hfp_r ⟨m, hm⟩
      have hcur_m : sr.mem (curParentBase ws n + m) = (q[m]).1 := hcur_r ⟨m, hm⟩
      have hbe_m : sr.mem (frameBEntryBase ws n k + m) = optFinIdx bEntry[m] := hbe_r ⟨m, hm⟩
      have hout_eq :
          (if sr.mem (frameMaskBase ws n k + m) = 1 then
            if optFinIdx bExit[(q[x0.1]).1] < n then
              if m = optFinIdx bExit[(q[x0.1]).1] then (q[x0.1]).1
              else sr.mem (frameParentBase ws n k + m)
            else sr.mem (frameParentBase ws n k + m)
          else if sr.mem (curParentBase ws n + m) = x0.1 then
            if sr.mem (frameBEntryBase ws n k + m) < n then
              sr.mem (frameBEntryBase ws n k + m)
            else m
          else sr.mem (curParentBase ws n + m)) =
            ((expandParentTable f inCycle bEntry bExit x0 q)[m]).1 := by
        rw [hm_m, hfp_m, hcur_m, hbe_m,
          show (expandParentTable f inCycle bEntry bExit x0 q)[m] =
            (expandParentTable f inCycle bEntry bExit x0 q)[(⟨m, hm⟩ : Fin n).1] from rfl,
          getElem_expandParentTable]
        dsimp only
        cases hvC : inCycle[m]
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one, beq_iff_eq, Fin.ext_iff]
          by_cases hqx : (q[m]).1 = x0.1
          · simp only [hqx, ↓reduceIte]
            cases bEntry[m] with
            | none => simp [optFinIdx]
            | some ys => simp [optFinIdx, ys.isLt]
          · simp [hqx]
        · simp only [↓reduceIte, beq_iff_eq, Fin.ext_iff]
          cases bExit[(q[x0.1]).1] with
          | none => simp [optFinIdx]
          | some xs =>
            simp only [optFinIdx, xs.isLt, ↓reduceIte]
            by_cases hmx : m = xs.1 <;> simp [hmx]
      refine ⟨by dsimp only [ExpandRowStepSafe, ra]; exact ⟨hm, hk, hws⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold expandRowStep
        dsimp only [ra]
        refine validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr_r ⊢; nlinarith)
            (validHistory_read_bind
              (by dsimp only [wsSize, curParentBase] at hf hfr_r ⊢; nlinarith)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf hfr_r ⊢; nlinarith) ?_)))
        refine validHistory_write_bind
          (by dsimp only [wsSize, nextParentBase] at hf hfr_r ⊢; nlinarith) ?_
          (validHistory_pure w _ _)
        rw [hout_eq]
        exact hws.of_le (by
          have := ((expandParentTable f inCycle bEntry bExit x0 q)[m]).isLt
          dsimp only [wsSize]; nlinarith)
      · unfold expandRowStep
        dsimp only [ra]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [expandRowStep, ra, client_simps]
      · intro addr haddr
        dsimp only [nextParentBase] at haddr
        simp only [expandRowStep, ra, client_simps, nextParentBase]
        exact Function.update_of_ne (by omega) _ _
      · unfold expandRowStep
        dsimp only [ra]
        simp only [client_simps]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_, ?_, ?_⟩
        · intro v
          have := v.isLt
          rw [Function.update_of_ne (by dsimp only [curParentBase, nextParentBase]; omega)]
          exact hcur_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameParentBase, frameBase, nextParentBase]; omega)]
          exact hfp_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, nextParentBase]; omega)]
          exact hm_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameBEntryBase, frameBase, nextParentBase]; omega)]
          exact hbe_r v
        · intro j hj
          by_cases hjm : j.1 = m
          · have hj_eq : j = ⟨m, hm⟩ := Fin.ext hjm
            subst hj_eq
            dsimp only
            rw [Function.update_self]
            exact hout_eq
          · rw [Function.update_of_ne (by omega)]
            exact hdone_r j (by omega))
    0 s₀ ⟨rfl, rfl, hcur, hfp, hm, hbe, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, hdone_end⟩ := hrow
  unfold fillExpandRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun j => hdone_end j j.isLt⟩

private theorem expandLevelProg_spec {w n ws k : ℕ} (x0 : Fin n)
    (f q : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hrep : s₀.mem (frameRepAddr ws n k) = x0.1)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q[v.1]).1)
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hm : ∀ v : Fin n, s₀.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0)
    (hbe : ∀ v : Fin n, s₀.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1])
    (hbx : ∀ v : Fin n, s₀.mem (frameBExitBase ws n k + v.1) = optFinIdx bExit[v.1]) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (expandLevelProg la)
    let p' := expandParentTable f inCycle bEntry bExit x0 q
    ExpandLevelSafe w la s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (expandLevelProg la)) ∧
      memoryCost (expandLevelProg la) s₀ ≤ 7 * n + 3 ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (p'[v.1]).1) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have hqx0 : s₀.mem (curParentBase ws n + x0.1) = (q[x0.1]).1 := hcur x0
  have hbx_qx0 : s₀.mem (frameBExitBase ws n k + (q[x0.1]).1) = optFinIdx bExit[(q[x0.1]).1] :=
    hbx q[x0.1]
  let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
  have hrow := fillExpandRowProg_spec x0 f q inCycle bEntry bExit s₀ hk hws hf hcur hfp hm hbe
  set s1 := (Memory.spec 0).clientState s₀ (fillExpandRowProg ra)
  let ca : CopyArgs := ⟨nextParentBase ws n, curParentBase ws n, n⟩
  have hcopy := copyWordsProg_spec ca s1
    (by dsimp only [ca, wsSize, nextParentBase] at hf ⊢; rw [hrow.2.2.2.1]; nlinarith)
    (by dsimp only [ca, wsSize, curParentBase] at hf ⊢; rw [hrow.2.2.2.1]; nlinarith)
    (Or.inr (by dsimp only [ca, curParentBase, nextParentBase]; omega))
    (hws.of_le (by dsimp only [ca, wsSize, nextParentBase]; nlinarith))
    (hws.of_le (by dsimp only [ca, wsSize, curParentBase]; nlinarith))
    (hws.of_le (by dsimp only [ca, wsSize]; nlinarith))
    (fun i hi => by
      dsimp only [ca]
      rw [hrow.2.2.2.2.2 ⟨i, hi⟩]
      exact hws.of_le (by
        have := ((expandParentTable f inCycle bEntry bExit x0 q)[i]).isLt
        dsimp only [wsSize]; nlinarith))
  have hsafe : ExpandLevelSafe w la s₀ := by
    dsimp only [ExpandLevelSafe, la]
    rw [hrep, hqx0, hbx_qx0]
    exact ⟨hk, hws, x0.isLt, (q[x0.1]).isLt, hrow.1, hcopy.1⟩
  unfold expandLevelProg
  dsimp only [la]
  refine ⟨hsafe, ?_, ?_, ?_, ?_, ?_⟩
  · refine validHistory_read_bind
      (by dsimp only [wsSize, frameRepAddr, frameBase] at hf ⊢; nlinarith) ?_
    rw [hrep]
    refine validHistory_read_bind
      (by have := x0.isLt; dsimp only [wsSize, curParentBase] at hf ⊢; nlinarith) ?_
    rw [hqx0]
    refine validHistory_read_bind
      (by have := (q[x0.1]).isLt; dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢;
          nlinarith) ?_
    rw [hbx_qx0]
    exact validHistory_bind_step hrow.2.1 hcopy.2.1
  · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hrep,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hqx0,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hbx_qx0,
      memoryCost_bind']
    have hr_c : memoryCost (fillExpandRowProg ra) s₀ ≤ 5 * n := hrow.2.2.1
    have hc_c : memoryCost (copyWordsProg ca) s1 ≤ 2 * n := hcopy.2.2.1
    dsimp only [ra, ca, s1] at hr_c hc_c ⊢
    omega
  · have hcopy_fr := hcopy.2.2.2.1
    dsimp only [s1, ra] at hcopy_fr
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    exact hcopy_fr.trans hrow.2.2.2.1
  · intro addr haddr
    have hcopy_mod := hcopy.2.2.2.2.1
    dsimp only [s1, ra] at hcopy_mod
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    rw [hcopy_mod addr (by dsimp only [ca, curParentBase, nextParentBase] at haddr ⊢; omega)]
    exact hrow.2.2.2.2.1 addr (by dsimp only [curParentBase, nextParentBase] at haddr ⊢; omega)
  · intro v
    have hcopy_val := hcopy.2.2.2.2.2
    dsimp only [s1, ra] at hcopy_val
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    rw [show curParentBase ws n + v.1 = ca.dst + v.1 from rfl, hcopy_val v.1 v.isLt]
    exact hrow.2.2.2.2.2 v


/-! ### Full solver `edmondsCoreProg_spec`, entry programs, and `O(n³)` Word-RAM theorems -/

private structure LevelFrame (n : ℕ) where
  parents : ParentTable n
  inCycle : Vector Bool n
  bEntry : Vector (Option (Fin n)) n
  bExit : Vector (Option (Fin n)) n
  x0 : Fin n

private def expandFrames {n : ℕ} : List (LevelFrame n) → ParentTable n → ParentTable n
  | [], q => q
  | fr :: rest, q =>
    expandParentTable fr.parents fr.inCycle fr.bEntry fr.bExit fr.x0 (expandFrames rest q)

private theorem expandFrames_append_singleton {n : ℕ} (frs : List (LevelFrame n))
    (fr : LevelFrame n) (q : ParentTable n) :
    expandFrames (frs ++ [fr]) q =
      expandFrames frs (expandParentTable fr.parents fr.inCycle fr.bEntry fr.bExit fr.x0 q) := by
  induction frs with
  | nil => rfl
  | cons _ _ ih => simp [expandFrames, ih]

private def FrameStored (ws n k : ℕ) (fr : LevelFrame n) (s : Memory.State) : Prop :=
  s.mem (frameRepAddr ws n k) = fr.x0.1 ∧
    (∀ v : Fin n, s.mem (frameParentBase ws n k + v.1) = (fr.parents[v.1]).1) ∧
    (∀ v : Fin n, s.mem (frameMaskBase ws n k + v.1) = if fr.inCycle[v.1] then 1 else 0) ∧
    (∀ v : Fin n, s.mem (frameBEntryBase ws n k + v.1) = optFinIdx fr.bEntry[v.1]) ∧
    (∀ v : Fin n, s.mem (frameBExitBase ws n k + v.1) = optFinIdx fr.bExit[v.1])

private theorem frameStored_congr {ws n k : ℕ} {fr : LevelFrame n} {s₁ s₂ : Memory.State}
    (h : FrameStored ws n k fr s₁)
    (heq : ∀ addr, frameBase ws n k ≤ addr → addr < frameBase ws n k + (4 * n + 1) →
      s₂.mem addr = s₁.mem addr) :
    FrameStored ws n k fr s₂ := by
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [heq _ (by dsimp only [frameRepAddr]; omega) (by dsimp only [frameRepAddr]; omega)]
    exact h.1
  · have := v.isLt
    rw [heq _ (by dsimp only [frameParentBase]; omega) (by dsimp only [frameParentBase]; omega)]
    exact h.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameMaskBase]; omega) (by dsimp only [frameMaskBase]; omega)]
    exact h.2.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameBEntryBase]; omega) (by dsimp only [frameBEntryBase]; omega)]
    exact h.2.2.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameBExitBase]; omega) (by dsimp only [frameBExitBase]; omega)]
    exact h.2.2.2.2 v

private structure ContractRoundDisj (ws n k : ℕ) : Prop where
  fp_rep : ∀ v : Fin n, frameParentBase ws n k + v.1 ≠ frameRepAddr ws n k
  adj_rep : ∀ u col : Fin n, curAdjBase ws n + u.1 * n + col.1 ≠ frameRepAddr ws n k
  cost_rep : ∀ u col : Fin n, curCostBase ws n + u.1 * n + col.1 ≠ frameRepAddr ws n k
  adj_cm : ∀ u col : Fin n,
    ¬(frameMaskBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
      curAdjBase ws n + u.1 * n + col.1 < frameMaskBase ws n k + n)
  cost_cm : ∀ u col : Fin n,
    ¬(frameMaskBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
      curCostBase ws n + u.1 * n + col.1 < frameMaskBase ws n k + n)
  fp_cm : ∀ v : Fin n,
    ¬(frameMaskBase ws n k ≤ frameParentBase ws n k + v.1 ∧
      frameParentBase ws n k + v.1 < frameMaskBase ws n k + n)
  adj_be : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < frameBEntryBase ws n k + n))
  cost_be : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < frameBEntryBase ws n k + n))
  mask_be : ∀ y : Fin n,
    ¬((candPredBase ws n ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < frameBEntryBase ws n k + n))
  fp_be : ∀ v : Fin n,
    ¬((candPredBase ws n ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < frameBEntryBase ws n k + n))
  adj_bx : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < frameBExitBase ws n k + n))
  cost_bx : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < frameBExitBase ws n k + n))
  mask_bx : ∀ y : Fin n,
    ¬((candPredBase ws n ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < frameBExitBase ws n k + n))
  fp_bx : ∀ v : Fin n,
    ¬((candPredBase ws n ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < frameBExitBase ws n k + n))
  be_bx : ∀ u : Fin n,
    ¬((candPredBase ws n ≤ frameBEntryBase ws n k + u.1 ∧
        frameBEntryBase ws n k + u.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameBEntryBase ws n k + u.1 ∧
        frameBEntryBase ws n k + u.1 < frameBExitBase ws n k + n))
  out : ∀ addr,
    ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
      (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
    ¬(ws ≤ addr ∧ addr < ws + 4 * (n * n)) ∧
    ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n)) ∧
    ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n)) ∧
    ¬(frameMaskBase ws n k ≤ addr ∧ addr < frameMaskBase ws n k + n) ∧
    addr ≠ frameRepAddr ws n k
  rep_all :
    ¬(ws ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < ws + 4 * (n * n)) ∧
    ¬((candPredBase ws n ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameRepAddr ws n k ∧
        frameRepAddr ws n k < frameBExitBase ws n k + n)) ∧
    ¬((candPredBase ws n ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameRepAddr ws n k ∧
        frameRepAddr ws n k < frameBEntryBase ws n k + n)) ∧
    ¬(frameMaskBase ws n k ≤ frameRepAddr ws n k ∧
      frameRepAddr ws n k < frameMaskBase ws n k + n)
  fp_ct : ∀ v : Fin n,
    ¬(ws ≤ frameParentBase ws n k + v.1 ∧ frameParentBase ws n k + v.1 < ws + 4 * (n * n))
  ct_mask : ∀ v : Fin n,
    ¬(ws ≤ frameMaskBase ws n k + v.1 ∧ frameMaskBase ws n k + v.1 < ws + 4 * (n * n))
  ct_be : ∀ v : Fin n,
    ¬(ws ≤ frameBEntryBase ws n k + v.1 ∧ frameBEntryBase ws n k + v.1 < ws + 4 * (n * n))
  ct_bx : ∀ v : Fin n,
    ¬(ws ≤ frameBExitBase ws n k + v.1 ∧ frameBExitBase ws n k + v.1 < ws + 4 * (n * n))

private theorem contractRoundDisj (ws n k : ℕ) : ContractRoundDisj ws n k where
  fp_rep v := by have := v.isLt; dsimp only [frameParentBase, frameRepAddr, frameBase]; omega
  adj_rep u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curAdjBase, frameRepAddr, frameBase]; omega
  cost_rep u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curCostBase, frameRepAddr, frameBase]; omega
  adj_cm u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curAdjBase, frameMaskBase, frameBase]; omega
  cost_cm u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curCostBase, frameMaskBase, frameBase]; omega
  fp_cm v := by have := v.isLt; dsimp only [frameParentBase, frameMaskBase, frameBase]; omega
  adj_be u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curAdjBase, candPredBase, candCostBase, frameBEntryBase, frameBase]; omega
  cost_be u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curCostBase, candPredBase, candCostBase, frameBEntryBase, frameBase]; omega
  mask_be y := by
    have := y.isLt
    dsimp only [frameMaskBase, candPredBase, candCostBase, frameBEntryBase, frameBase]; omega
  fp_be v := by
    have := v.isLt
    dsimp only [frameParentBase, candPredBase, candCostBase, frameBEntryBase, frameBase]; omega
  adj_bx u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curAdjBase, candPredBase, candCostBase, frameBExitBase, frameBase]; omega
  cost_bx u col := by
    have := List.mul_add_lt_sq u.isLt col.isLt
    dsimp only [curCostBase, candPredBase, candCostBase, frameBExitBase, frameBase]; omega
  mask_bx y := by
    have := y.isLt
    dsimp only [frameMaskBase, candPredBase, candCostBase, frameBExitBase, frameBase]; omega
  fp_bx v := by
    have := v.isLt
    dsimp only [frameParentBase, candPredBase, candCostBase, frameBExitBase, frameBase]; omega
  be_bx u := by
    have := u.isLt
    dsimp only [frameBEntryBase, candPredBase, candCostBase, frameBExitBase, frameBase]; omega
  out addr haddr := by
    dsimp only [candPredBase, candCostBase, frameMaskBase, frameBEntryBase,
      frameBExitBase, frameRepAddr, frameBase] at haddr ⊢
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  rep_all := by
    dsimp only [candPredBase, candCostBase, frameMaskBase, frameBEntryBase,
      frameBExitBase, frameRepAddr, frameBase]
    exact ⟨by omega, by omega, by omega, by omega⟩
  fp_ct v := by dsimp only [frameParentBase, frameBase]; omega
  ct_mask v := by dsimp only [frameMaskBase, frameBase]; omega
  ct_be v := by dsimp only [frameBEntryBase, frameBase]; omega
  ct_bx v := by dsimp only [frameBExitBase, frameBase]; omega

private theorem matrix_mem_congr {n base : ℕ} {P : ℕ → Prop} {s₁ s₂ : Memory.State}
    {val : Fin n → Fin n → ℕ}
    (hmod : ∀ addr, ¬P addr → s₂.mem addr = s₁.mem addr)
    (hdisj : ∀ u col : Fin n, ¬P (base + u.1 * n + col.1))
    (hprev : ∀ u col : Fin n, s₁.mem (base + u.1 * n + col.1) = val u col) :
    ∀ u col : Fin n, s₂.mem (base + u.1 * n + col.1) = val u col := fun u col =>
  (hmod _ (hdisj u col)).trans (hprev u col)

private theorem vec_mem_congr {n base : ℕ} {P : ℕ → Prop} {s₁ s₂ : Memory.State}
    {val : Fin n → ℕ}
    (hmod : ∀ addr, ¬P addr → s₂.mem addr = s₁.mem addr)
    (hdisj : ∀ x : Fin n, ¬P (base + x.1))
    (hprev : ∀ x : Fin n, s₁.mem (base + x.1) = val x) :
    ∀ x : Fin n, s₂.mem (base + x.1) = val x := fun x =>
  (hmod _ (hdisj x)).trans (hprev x)

private theorem contractRoundBodyProg_spec {w n ws k B_k : ℕ} (r x0 : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (contractRoundBodyProg ca)
    let inCycle := cycleMask f x0
    let bEntry := bestEntryTable a c inCycle
    let bExit := reducedBestExitTable a c f inCycle
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    ContractRoundBodySafe w ca s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (contractRoundBodyProg ca)) ∧
      memoryCost (contractRoundBodyProg ca) s₀ ≤ 36 * (n * n) + 8 * n + 1 ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
        (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if a'[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c'[u.1][col.1]) ∧
      FrameStored ws n k ⟨f, inCycle, bEntry, bExit, x0⟩ s' := by
  let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
  have hd := contractRoundDisj ws n k
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfr_le := frame_le_frames hk
  have hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1]) := by
    intro u col
    have hb := hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [hb])
  have hrep_lt_fr : frameRepAddr ws n k < s₀.frontier := by
    dsimp only [wsSize, frameRepAddr, frameBase] at hf ⊢; linarith only [hf, hfr_le]
  have hx0_fit : Fits w x0.1 := hws.of_le (by have := x0.isLt; dsimp only [wsSize]; omega)
  let s0 : Memory.State := ⟨Function.update s₀.mem (frameRepAddr ws n k) x0.1, s₀.frontier⟩
  have hs0_mod : ∀ addr, ¬(addr = frameRepAddr ws n k) → s0.mem addr = s₀.mem addr :=
    fun _ hne => Function.update_of_ne hne _ _
  have hfp0 := vec_mem_congr hs0_mod hd.fp_rep hfp
  have ha0 := matrix_mem_congr hs0_mod hd.adj_rep ha
  have hc0 := matrix_mem_congr hs0_mod hd.cost_rep hc
  have hcm := cycleMaskProg_spec (parentBase := frameParentBase ws n k)
    (maskBase := frameMaskBase ws n k) f x0 s0 h1
    (hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le]))
    (hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; linarith only [hfr_le]))
    (hws.of_le (by dsimp only [wsSize]; omega))
    (by dsimp only [s0, wsSize, frameParentBase, frameBase] at hf ⊢; linarith only [hf, hfr_le])
    (by dsimp only [s0, wsSize, frameMaskBase, frameBase] at hf ⊢; linarith only [hf, hfr_le])
    (Or.inl (by dsimp only [frameParentBase, frameMaskBase, frameBase]; omega))
    hfp0
  let cmArgs : CycleMaskArgs := ⟨n, frameParentBase ws n k, frameMaskBase ws n k, x0.1⟩
  dsimp only at hcm
  generalize hs1 : (Memory.spec 0).clientState s0 (cycleMaskProg cmArgs) = s1 at hcm
  generalize hinC : cycleMask f x0 = inCycle at hcm
  have hs1_fr : s1.frontier = s₀.frontier := hcm.2.2.2.1
  have ha1 := matrix_mem_congr hcm.2.2.2.2.1 hd.adj_cm ha0
  have hc1 := matrix_mem_congr hcm.2.2.2.2.1 hd.cost_cm hc0
  have hfp1 := vec_mem_congr hcm.2.2.2.2.1 hd.fp_cm hfp0
  have hm1 := hcm.2.2.2.2.2
  have hbe := bestEntryProg_spec r.pos a c inCycle s1 hk hws
    (by rw [hs1_fr]; exact hf) ha1 hc1 hm1 hfit_c
  let lvArgs : LevelArgs := ⟨n, ws, k⟩
  dsimp only at hbe
  generalize hs2 : (Memory.spec 0).clientState s1 (bestEntryProg lvArgs) = s2 at hbe
  generalize hbEn : bestEntryTable a c inCycle = bEntry at hbe
  have hs2_fr : s2.frontier = s₀.frontier := hbe.2.2.2.1.trans hs1_fr
  have ha2 := matrix_mem_congr hbe.2.2.2.2.1 hd.adj_be ha1
  have hc2 := matrix_mem_congr hbe.2.2.2.2.1 hd.cost_be hc1
  have hm2 := vec_mem_congr hbe.2.2.2.2.1 hd.mask_be hm1
  have hfp2 := vec_mem_congr hbe.2.2.2.2.1 hd.fp_be hfp1
  have hbx := bestExitProg_spec r.pos a c f inCycle
    s2 hk hws (by rw [hs2_fr]; exact hf) hfit_diff ha2 hc2 hm2 hfp2 hB
  dsimp only at hbx
  generalize hs3 : (Memory.spec 0).clientState s2 (bestExitProg lvArgs) = s3 at hbx
  generalize hbEx : reducedBestExitTable a c f inCycle = bExit at hbx
  have hs3_fr : s3.frontier = s₀.frontier := hbx.2.2.2.1.trans hs2_fr
  have ha3 := matrix_mem_congr hbx.2.2.2.2.1 hd.adj_bx ha2
  have hc3 := matrix_mem_congr hbx.2.2.2.2.1 hd.cost_bx hc2
  have hm3 := vec_mem_congr hbx.2.2.2.2.1 hd.mask_bx hm2
  have hfp3 := vec_mem_congr hbx.2.2.2.2.1 hd.fp_bx hfp2
  have hbe3 := vec_mem_congr hbx.2.2.2.2.1 hd.be_bx hbe.2.2.2.2.2
  have hct := contractTablesProg_spec r x0 a c f inCycle bEntry bExit s3
    hk hws (by rw [hs3_fr]; exact hf) hfit_diff ha3 hc3 hm3 hfp3 hbe3 hbx.2.2.2.2.2 hB
  dsimp only at hct
  generalize hs4 : (Memory.spec 0).clientState s3 (contractTablesProg ca) = s4 at hct
  have hs4_fr : s4.frontier = s₀.frontier := hct.2.2.2.1.trans hs3_fr
  have hs4_mod : ∀ addr,
      ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
        (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
      s4.mem addr = s₀.mem addr := fun addr haddr => by
    obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hd.out addr haddr
    rw [hct.2.2.2.2.1 addr hd1, hbx.2.2.2.2.1 addr hd2, hbe.2.2.2.2.1 addr hd3,
      hcm.2.2.2.2.1 addr hd4]
    exact Function.update_of_ne hd5 _ _
  have hs4_frame : FrameStored ws n k ⟨f, inCycle, bEntry, bExit, x0⟩ s4 := by
    refine ⟨?_, vec_mem_congr hct.2.2.2.2.1 hd.fp_ct hfp3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_mask hm3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_be hbe3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_bx hbx.2.2.2.2.2⟩
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hd.rep_all
    rw [hct.2.2.2.2.1 _ hr1, hbx.2.2.2.2.1 _ hr2, hbe.2.2.2.2.1 _ hr3, hcm.2.2.2.2.1 _ hr4]
    exact Function.update_self _ _ _
  have hst_eq : (Memory.spec 0).clientState s₀ (contractRoundBodyProg ca) = s4 := by
    unfold contractRoundBodyProg
    dsimp only [ca]
    rw [StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s0
      (cycleMaskProg cmArgs >>= fun _ => bestEntryProg lvArgs >>= fun _ =>
        bestExitProg lvArgs >>= fun _ => contractTablesProg ca) = s4
    rw [StateTransitionSpec.clientState_bind, hs1,
      StateTransitionSpec.clientState_bind, hs2,
      StateTransitionSpec.clientState_bind, hs3, hs4]
  subst hbEx hbEn hinC
  refine ⟨?_, ?_, ?_, hst_eq ▸ hs4_fr, fun addr haddr => hst_eq ▸ hs4_mod addr haddr,
    fun u col => hst_eq ▸ hct.2.2.2.2.2.1 u col,
    fun u col => hst_eq ▸ hct.2.2.2.2.2.2 u col,
    hst_eq ▸ hs4_frame⟩
  · subst hs4 hs3 hs2 hs1
    exact ⟨hk, hws, hcm.1.1, hcm.1.2, hbe.1, hbx.1, hct.1.1, hct.1.2⟩
  · subst hs4 hs3 hs2 hs1
    unfold contractRoundBodyProg
    dsimp only [ca]
    exact validHistory_write_bind hrep_lt_fr hx0_fit
      (validHistory_bind_step hcm.2.1
        (validHistory_bind_step hbe.2.1
          (validHistory_bind_step hbx.2.1 hct.2.1)))
  · have c1 := hcm.2.2.1
    have c2 := hbe.2.2.1
    have c3 := hbx.2.2.1
    have c4 := hct.2.2.1
    unfold contractRoundBodyProg
    dsimp only [ca]
    rw [memoryCost_bind', memoryCost_write]
    change 1 + memoryCost
      (cycleMaskProg cmArgs >>= fun _ => bestEntryProg lvArgs >>= fun _ =>
        bestExitProg lvArgs >>= fun _ => contractTablesProg ca) s0 ≤ _
    rw [memoryCost_bind', hs1, memoryCost_bind', hs2, memoryCost_bind', hs3]
    dsimp only [cmArgs, lvArgs, ca] at c1 c2 c3 c4 ⊢
    nlinarith only [c1, c2, c3, c4]

private theorem backwardProg_spec {w n ws depth : ℕ} (hpos : 0 < n)
    (frs : List (LevelFrame n)) (q₀ : ParentTable n) (s₀ : Memory.State)
    (hdepth_le : depth ≤ n) (hlen : frs.length = depth)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q₀[v.1]).1)
    (hfrs : ∀ k (hk : k < frs.length), FrameStored ws n k frs[k] s₀) :
    let ba : BackwardArgs := ⟨n, ws, depth⟩
    let s' := (Memory.spec 0).clientState s₀ (backwardProg ba)
    let pFinal := expandFrames frs q₀
    iterationSafe backwardStep BackwardStepSafe w ba depth 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (backwardProg ba)) ∧
      memoryCost (backwardProg ba) s₀ ≤ (7 * n + 4) * depth ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (pFinal[v.1]).1) := by
  let ba : BackwardArgs := ⟨n, ws, depth⟩
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith only [hf, hpos]
  have h := iterate_spec backwardStep BackwardStepSafe w ba (7 * n + 4) depth
    (fun j idx s =>
      idx = j ∧ s.frontier = s₀.frontier ∧
        (∀ k (hk : k < frs.length), FrameStored ws n k frs[k] s) ∧
        (∀ v : Fin n,
          s.mem (curParentBase ws n + v.1) = ((expandFrames (frs.drop (depth - j)) q₀)[v.1]).1))
    (fun addr => curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n)
    (fun j hj idx s ⟨hidx, hfr, hfrs_s, hcur_s⟩ => by
      subst idx
      set k := depth - (j + 1)
      have hk_d : k < depth := by omega
      have hk_n : k < n := lt_of_lt_of_le hk_d hdepth_le
      have hk_len : k < frs.length := hlen ▸ hk_d
      have hstored := hfrs_s k hk_len
      set fr := frs[k]
      set q_j := expandFrames (frs.drop (depth - j)) q₀
      have hexp := expandLevelProg_spec fr.x0 fr.parents q_j fr.inCycle fr.bEntry fr.bExit s
        hk_n hws (by rw [hfr]; exact hf) hstored.1 hcur_s hstored.2.1 hstored.2.2.1
        hstored.2.2.2.1 hstored.2.2.2.2
      have hdrop_eq : frs.drop k = fr :: frs.drop (depth - j) := by
        have h1 : depth - j = k + 1 := by omega
        rw [h1, ← List.cons_getElem_drop_succ (h := hk_len)]
      refine ⟨by dsimp only [BackwardStepSafe, ba]; exact ⟨by omega,
          hws.of_le (by dsimp only [wsSize]; omega), hexp.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold backwardStep
        dsimp only [ba]
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hexp.2.1 (validHistory_pure w _ _))
      · unfold backwardStep
        dsimp only [ba]
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_e : memoryCost (expandLevelProg ⟨n, ws, k⟩) s ≤ 7 * n + 3 := hexp.2.2.1
        dsimp only [k] at hc_e
        simp only [client_simps]
        omega
      · unfold backwardStep
        dsimp only [ba]
        have hexp_fr := hexp.2.2.2.1
        dsimp only [k] at hexp_fr ⊢
        simp [client_simps, hexp_fr, hfr]
      · intro addr haddr
        unfold backwardStep
        dsimp only [ba]
        have hexp_mod := hexp.2.2.2.2.1
        dsimp only [k] at hexp_mod ⊢
        simp only [client_simps]
        exact hexp_mod addr haddr
      · unfold backwardStep
        dsimp only [ba]
        have hexp_fr := hexp.2.2.2.1
        have hexp_mod := hexp.2.2.2.2.1
        have hexp_val := hexp.2.2.2.2.2
        dsimp only [k] at hexp_fr hexp_mod hexp_val ⊢
        simp only [client_simps]
        refine ⟨trivial, hexp_fr.trans hfr, ?_, ?_⟩
        · intro m hm
          exact frameStored_congr (hfrs_s m hm) fun addr hlo hhi =>
            hexp_mod addr (by
              dsimp only [curParentBase, nextParentBase, frameBase] at hlo ⊢; omega)
        · intro v
          change ((Memory.spec 0).clientState s (expandLevelProg ⟨n, ws, depth - (j + 1)⟩)).mem
            (curParentBase ws n + v.1) = ((expandFrames (frs.drop (depth - (j + 1))) q₀)[v.1]).1
          rw [show depth - (j + 1) = k from rfl, hdrop_eq]
          exact hexp_val v)
    0 s₀ ⟨rfl, rfl, hfrs, fun v => by
      have hdrop_all : frs.drop depth = [] := by simp [hlen]
      simpa [hdrop_all, expandFrames] using hcur v⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, hcur_end⟩ := h
  unfold backwardProg
  refine ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun v => ?_⟩
  simpa [Nat.sub_self] using hcur_end v

private theorem forwardStep_contract_math {n k M₀ : ℕ} {r x0 : Fin n}
    {a₀ a_k : AdjTable n} {c₀ cUnred cRed : CostTable ℤ n} {frs : List (LevelFrame n)}
    (hk : k < n) (hpot : RowPotEq a_k cUnred cRed)
    (heq_aux : edmondsTableAux r n a₀ c₀ =
      (edmondsTableAux r (n - k) a_k cUnred).map (expandFrames frs))
    (hfeas_b : (selectParents a_k cRed r).feasible = true)
    (hcyc_case : findCycleTable r (selectParents a_k cRed r).parents = some x0)
    (hbnd_k : ∀ u col : Fin n, -(M₀ : ℤ) ≤ cRed[u.1][col.1] ∧
      cRed[u.1][col.1] ≤ (k + 1 : ℤ) * M₀) :
    let f_k := (selectParents a_k cRed r).parents
    let inCycle := cycleMask f_k x0
    let bEntry := bestEntryTable a_k cRed inCycle
    let bExit := reducedBestExitTable a_k cRed f_k inCycle
    let other := otherCycleCost cUnred f_k inCycle
    let a' := contractAdjTable a_k inCycle bEntry bExit x0 r
    let cUnred' := contractCostTable cUnred inCycle other bEntry bExit x0
    let cRed' := contractReducedCostTable a_k cRed f_k inCycle bEntry bExit x0
    let newFr : LevelFrame n := ⟨f_k, inCycle, bEntry, bExit, x0⟩
    RowPotEq a' cUnred' cRed' ∧
      edmondsTableAux r n a₀ c₀ =
        (edmondsTableAux r (n - (k + 1)) a' cUnred').map (expandFrames (frs ++ [newFr])) ∧
      ∀ u col : Fin n, -(M₀ : ℤ) ≤ cRed'[u.1][col.1] ∧
        cRed'[u.1][col.1] ≤ ((k + 1 : ℕ) + 1 : ℤ) * M₀ := by
  have hsel_eq_unred : selectParents a_k cRed r = selectParents a_k cUnred r :=
    selectParents_of_rowPotEq r hpot
  obtain ⟨hfr_root, hfeas_v⟩ := selectParents_feasible_spec a_k cRed r hfeas_b
  obtain ⟨hx0_in, hnot_r⟩ :=
    not_inCycle_root r (selectParents a_k cRed r).parents hfr_root hcyc_case
  let f_k := (selectParents a_k cRed r).parents
  let inCycle := cycleMask f_k x0
  have hact : ∀ x : Fin n, inCycle[x.1] = true → a_k[x.1][f_k[x.1].1] = true :=
    fun x hx => (hfeas_v x (hnot_r x hx)).1
  have hopt : ∀ x : Fin n, inCycle[x.1] = true →
      ∀ w : Fin n, a_k[x.1][w.1] = true → w ≠ x → cRed[x.1][f_k[x.1].1] ≤ cRed[x.1][w.1] :=
    fun x hx => (hfeas_v x (hnot_r x hx)).2.2
  have hbe_eq : bestEntryTable a_k cRed inCycle = bestEntryTable a_k cUnred inCycle :=
    bestEntryTable_of_rowPotEq inCycle hpot
  have hbx_eq : reducedBestExitTable a_k cRed f_k inCycle =
      bestExitTable a_k cUnred inCycle (otherCycleCost cUnred f_k inCycle) :=
    reducedBestExitTable_eq_bestExitTable hpot hact
  have hfuel_eq : n - k = (n - (k + 1)) + 1 := by omega
  refine ⟨rowPotEq_contractReduced hpot hx0_in hact, ?_, fun u col => ?_⟩
  · rw [heq_aux, hfuel_eq]
    dsimp only [f_k, inCycle] at hbe_eq hbx_eq ⊢
    simp only [edmondsTableAux, ← hsel_eq_unred, hfeas_b, ↓reduceIte, hcyc_case, ← hbe_eq,
      ← hbx_eq, Option.map_map]
    congr 1
    funext q
    exact (expandFrames_append_singleton frs ⟨(selectParents a_k cRed r).parents,
      cycleMask (selectParents a_k cRed r).parents x0,
      bestEntryTable a_k cRed (cycleMask (selectParents a_k cRed r).parents x0),
      reducedBestExitTable a_k cRed (selectParents a_k cRed r).parents
        (cycleMask (selectParents a_k cRed r).parents x0), x0⟩ q).symm
  · have hb := contractReducedCostTable_bounds (bEntry := bestEntryTable a_k cRed inCycle)
      (x0 := x0) hbnd_k hopt u col
    exact ⟨hb.1, by push_cast; linarith only [hb.2]⟩

private theorem forwardProg_spec {w n ws M₀ : ℕ} (r : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hwb : Fits w (wordBound n M₀))
    (ha₀ : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0)
    (hc₀ : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1])
    (hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀) :
    let ca : CoreArgs := ⟨n, r.1, ws⟩
    let res := (Memory.spec 0).clientResult s₀ (forwardProg ca)
    let s1 := (Memory.spec 0).clientState s₀ (forwardProg ca)
    iterationSafe forwardStep ForwardStepSafe w ca n ⟨0, 0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (forwardProg ca)) ∧
      memoryCost (forwardProg ca) s₀ ≤ (43 * (n * n) + 11 * n + 2) * n ∧
      s1.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + wsSize n) → s1.mem addr = s₀.mem addr) ∧
      ((res.status = 1 ∧ res.depth ≤ n ∧
          ∃ (frs : List (LevelFrame n)) (q₀ : ParentTable n),
            frs.length = res.depth ∧
            edmondsTableAux r n a₀ c₀ = some (expandFrames frs q₀) ∧
            (∀ v : Fin n, s1.mem (curParentBase ws n + v.1) = (q₀[v.1]).1) ∧
            (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s1)) ∨
        (res.status ≠ 1 ∧ edmondsTableAux r n a₀ c₀ = none)) := by
  let ca : CoreArgs := ⟨n, r.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by
    have hr_pos := r.pos
    dsimp only [wsSize] at hf
    nlinarith only [hf, hr_pos]
  have hdiff_fit : ∀ k < n, Fits w (4 * ((k + 1) * M₀) + 2) := by
    intro k hk
    have hmul : (k + 1) * M₀ ≤ (n + 1) * M₀ := Nat.mul_le_mul_right M₀ (by omega)
    have hsq1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
    exact hwb.of_le (by dsimp only [wordBound]; linarith only [hmul, hsq1])
  have h := iterate_spec forwardStep ForwardStepSafe w ca (43 * (n * n) + 11 * n + 2) n
    (fun k st s =>
      st.k = k ∧ s.frontier = s₀.frontier ∧
        ((st.status = 0 ∧ st.depth = k ∧
            ∃ (a_k : AdjTable n) (cUnred cRed : CostTable ℤ n) (frs : List (LevelFrame n)),
              frs.length = k ∧
              RowPotEq a_k cUnred cRed ∧
              edmondsTableAux r n a₀ c₀ =
                (edmondsTableAux r (n - k) a_k cUnred).map (expandFrames frs) ∧
              (∀ u col : Fin n,
                s.mem (curAdjBase ws n + u.1 * n + col.1) = if a_k[u.1][col.1] then 1 else 0) ∧
              (∀ u col : Fin n,
                s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode cRed[u.1][col.1]) ∧
              (∀ u col : Fin n,
                -(M₀ : ℤ) ≤ cRed[u.1][col.1] ∧ cRed[u.1][col.1] ≤ (k + 1 : ℤ) * M₀) ∧
              (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s)) ∨
          (st.status = 1 ∧ st.depth ≤ k ∧
            ∃ (frs : List (LevelFrame n)) (q₀ : ParentTable n),
              frs.length = st.depth ∧
              edmondsTableAux r n a₀ c₀ = some (expandFrames frs q₀) ∧
              (∀ v : Fin n, s.mem (curParentBase ws n + v.1) = (q₀[v.1]).1) ∧
              (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s)) ∨
          (st.status = 2 ∧ edmondsTableAux r n a₀ c₀ = none)))
    (fun addr => ws ≤ addr ∧ addr < ws + wsSize n)
    (fun k hk st s ⟨hst_k, hfr, hbranch⟩ => by
      rcases st with ⟨kIdx, status, depth⟩
      dsimp only at hst_k hbranch
      subst kIdx
      have hf_s : ws + wsSize n ≤ s.frontier := by rw [hfr]; exact hf
      have hf_s_pos : 0 < s.frontier := by rw [hfr]; exact hf_pos
      rcases hbranch with
          ⟨hst0, hdep, a_k, cUnred, cRed, frs, hlen, hpot, heq_aux, ha_k, hc_k, hbnd_k, hfrs_k⟩ |
          ⟨hst1, hdep, frs, q₀, hlen, heq_aux, hcur_k, hfrs_k⟩ | ⟨hst2, heq_none⟩
      · subst status depth
        have hfr_le_k := frame_le_frames hk
        have hfit_diff := hdiff_fit k hk
        have hB_k : ∀ u col : Fin n, (cRed[u.1][col.1]).natAbs ≤ (k + 1) * M₀ := by
          intro u col
          obtain ⟨hlo, hhi⟩ := hbnd_k u col
          have hlo' : -(((k + 1) * M₀ : ℕ) : ℤ) ≤ cRed[u.1][col.1] := by
            have : (M₀ : ℤ) ≤ (k + 1 : ℤ) * M₀ := by nlinarith
            push_cast
            linarith
          have hhi' : cRed[u.1][col.1] ≤ (((k + 1) * M₀ : ℕ) : ℤ) := by
            push_cast
            linarith
          omega
        have hfit_ck : ∀ u col : Fin n, Fits w (Signed.encode cRed[u.1][col.1]) := by
          intro u col
          have hbk := hB_k u col
          unfold Signed.encode
          exact hfit_diff.of_le (by split_ifs <;> omega)
        have hsel := selectParentsProg_spec r a_k cRed s hk hws hf_s ha_k hc_k hfit_ck
        set selArgs : SelectArgs := ⟨n, r.1, ws, k⟩
        set sSel := (Memory.spec 0).clientState s (selectParentsProg selArgs)
        set sel := selectParents a_k cRed r
        have hsel_eq_unred : selectParents a_k cRed r = selectParents a_k cUnred r :=
          selectParents_of_rowPotEq r hpot
        have hsSel_fr : sSel.frontier = s₀.frontier := hsel.2.2.2.1.trans hfr
        have hf_sSel : ws + wsSize n ≤ sSel.frontier := by rw [hsSel_fr]; exact hf
        have ha_sel : ∀ u col : Fin n,
            sSel.mem (curAdjBase ws n + u.1 * n + col.1) = if a_k[u.1][col.1] then 1 else 0 := by
          intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [hsel.2.2.2.2.1 _ (by
            dsimp only [curAdjBase, candPredBase, candCostBase, frameParentBase, frameBase]
            omega)]
          exact ha_k u col
        have hc_sel : ∀ u col : Fin n,
            sSel.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode cRed[u.1][col.1] := by
          intro u col
          have := List.mul_add_lt_sq u.isLt col.isLt
          rw [hsel.2.2.2.2.1 _ (by
            dsimp only [curCostBase, candPredBase, candCostBase, frameParentBase, frameBase]
            omega)]
          exact hc_k u col
        have hfrs_sel : ∀ j (hj : j < frs.length), FrameStored ws n j frs[j] sSel := fun j hj =>
          frameStored_congr (hfrs_k j hj) fun addr hlo hhi =>
            hsel.2.2.2.2.1 addr (by
              have hjk : j < k := hlen ▸ hj
              have hmul : j * (4 * n + 1) + (4 * n + 1) ≤ k * (4 * n + 1) := by
                simpa [Nat.succ_mul] using Nat.mul_le_mul_right (4 * n + 1) hjk
              dsimp only [candPredBase, candCostBase, frameParentBase, frameBase] at hlo hhi ⊢
              omega)
        have hfc := findCycleProg_spec r sel.parents sSel h1
          (hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le_k]))
          (hws.of_le (by dsimp only [wsSize]; omega))
          (by rw [hsSel_fr]; exact hf_pos)
          (by dsimp only [wsSize, frameParentBase, frameBase] at hf_sSel ⊢;
              linarith only [hf_sSel, hfr_le_k])
          hsel.2.2.2.2.2.2
        set fcArgs : FindCycleArgs := ⟨n, r.1, frameParentBase ws n k⟩
        have hsFc_eq : (Memory.spec 0).clientState sSel (findCycleProg fcArgs) = sSel :=
          hfc.2.2.2.1
        have hfuel_eq : n - k = (n - (k + 1)) + 1 := by omega
        have hcp_parent := copyWordsProg_spec
          ⟨frameParentBase ws n k, curParentBase ws n, n⟩ sSel
          (by dsimp only [wsSize, frameParentBase, frameBase] at hf_sSel ⊢;
              linarith only [hf_sSel, hfr_le_k])
          (by dsimp only [wsSize, curParentBase] at hf_sSel ⊢; omega)
          (Or.inr (by dsimp only [curParentBase, frameParentBase, frameBase]; omega))
          (hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le_k]))
          (hws.of_le (by dsimp only [wsSize, curParentBase]; omega))
          (hws.of_le (by dsimp only [wsSize]; omega))
          (fun i hi => by
            dsimp only
            rw [hsel.2.2.2.2.2.2 ⟨i, hi⟩]
            exact hws.of_le (by
              have := (sel.parents[i]).isLt
              dsimp only [wsSize]; omega))
        have hcrb_at (x0 : Fin n) :=
          contractRoundBodyProg_spec r x0 a_k cRed sel.parents sSel hk hws hf_sSel
            hfit_diff ha_sel hc_sel hsel.2.2.2.2.2.2 hB_k
        have hsafe_step : ForwardStepSafe w (ca, ⟨k, 0, k⟩) s := by
          dsimp only [ForwardStepSafe, ca]
          refine ⟨hk, hws, fun _ => ⟨hsel.1.2, fun _ => ⟨hfc.1, ?_, ?_⟩⟩⟩
          · intro _
            rw [hsFc_eq]
            exact hcp_parent.1
          · intro hx0_ne
            have hfc_s := hsFc_eq
            have hfc_r := hfc.2.2.2.2
            dsimp only [sSel, selArgs, fcArgs] at hfc_s hfc_r
            rw [hfc_s]
            rw [hfc_r] at hx0_ne ⊢
            cases hcyc_case : findCycleTable r sel.parents with
            | none => exact absurd (by simp [hcyc_case, optFinIdx]) hx0_ne
            | some x0 =>
              simp only [optFinIdx]
              exact (hcrb_at x0).1
        refine ⟨hsafe_step, ?_, ?_, ?_, ?_, ?_⟩
        · unfold forwardStep
          dsimp only [ca, ↓reduceIte]
          refine validHistory_read_bind hf_s_pos ?_
          refine validHistory_bind_step hsel.2.1 ?_
          by_cases hfeas0 : (Memory.spec 0).clientResult s (selectParentsProg selArgs) = 0
          · simp only [selArgs] at hfeas0
            simp only [hfeas0, ↓reduceIte]
            exact validHistory_pure w _ _
          · simp only [selArgs] at hfeas0
            simp only [hfeas0, ↓reduceIte]
            refine validHistory_bind_step hfc.2.1 ?_
            change (Memory.spec w).ValidHistory ((Memory.spec 0).clientState sSel
              (findCycleProg fcArgs)) _
            rw [hsFc_eq]
            by_cases hx0_eq : (Memory.spec 0).clientResult sSel (findCycleProg fcArgs) = n
            · dsimp only [fcArgs, sSel, selArgs] at hx0_eq ⊢
              simp only [hx0_eq, ↓reduceIte]
              exact validHistory_bind_step hcp_parent.2.1 (validHistory_pure w _ _)
            · have hfc_res := hfc.2.2.2.2
              dsimp only [fcArgs, sSel, selArgs] at hx0_eq hfc_res ⊢
              simp only [hx0_eq, ↓reduceIte]
              rw [hfc_res] at hx0_eq ⊢
              cases hcyc_case : findCycleTable r sel.parents with
              | none => simp [hcyc_case, optFinIdx] at hx0_eq
              | some x0 =>
                simp only [optFinIdx]
                exact validHistory_bind_step (hcrb_at x0).2.1 (validHistory_pure w _ _)
        · unfold forwardStep
          dsimp only [ca]
          rw [memoryCost_bind', memoryCost_read, clientState_read]
          simp only [↓reduceIte, memoryCost_bind']
          have hc_sel_le : memoryCost (selectParentsProg selArgs) s ≤ (6 * n + 2) * n :=
            hsel.2.2.1
          dsimp only [selArgs] at hc_sel_le
          split_ifs with hfeas0
          · simp only [client_simps]; nlinarith only [hc_sel_le]
          · simp only [memoryCost_bind']
            split_ifs with hx0_eq
            · have hc_fc_le : memoryCost (findCycleProg fcArgs) sSel ≤ (n + 1) * n := hfc.2.2.1
              have hc_cp_le := hcp_parent.2.2.1
              dsimp only [fcArgs, sSel, selArgs] at hc_fc_le hsFc_eq hc_cp_le ⊢
              rw [hsFc_eq]
              simp only [client_simps] at hc_cp_le ⊢
              nlinarith only [hc_sel_le, hc_fc_le, hc_cp_le]
            · have hc_fc_le : memoryCost (findCycleProg fcArgs) sSel ≤ (n + 1) * n := hfc.2.2.1
              have hfc_res := hfc.2.2.2.2
              dsimp only [fcArgs, sSel, selArgs] at hc_fc_le hsFc_eq hfc_res hx0_eq ⊢
              rw [hsFc_eq, hfc_res]
              rw [hfc_res] at hx0_eq
              cases hcyc_case : findCycleTable r sel.parents with
              | none => simp [hcyc_case, optFinIdx] at hx0_eq
              | some x0 =>
                simp only [optFinIdx]
                have hc_crb := (hcrb_at x0).2.2.1
                dsimp only [sSel, selArgs] at hc_crb
                simp only [client_simps]
                nlinarith only [hc_sel_le, hc_fc_le, hc_crb]
        · unfold forwardStep
          dsimp only [ca]
          simp only [client_simps, ↓reduceIte]
          split_ifs with hfeas0 hx0_eq
          · dsimp only [sSel, selArgs] at hsSel_fr
            simp [client_simps, hsSel_fr, hfr]
          · have hcp_fr := hcp_parent.2.2.2.1
            dsimp only [fcArgs, sSel, selArgs] at hsFc_eq hcp_fr hsSel_fr ⊢
            rw [hsFc_eq]
            simp [client_simps, hcp_fr, hsSel_fr, hfr]
          · have hfc_res := hfc.2.2.2.2
            dsimp only [fcArgs, sSel, selArgs] at hsFc_eq hfc_res hx0_eq ⊢
            rw [hsFc_eq, hfc_res]
            rw [hfc_res] at hx0_eq
            cases hcyc_case : findCycleTable r sel.parents with
            | none => simp [hcyc_case, optFinIdx] at hx0_eq
            | some x0 =>
              simp only [optFinIdx]
              have hcrb_fr := (hcrb_at x0).2.2.2.1
              dsimp only [sSel, selArgs] at hcrb_fr hsSel_fr
              simp [client_simps, hcrb_fr, hsSel_fr, hfr]
        · intro addr haddr
          have hsSel_addr : sSel.mem addr = s.mem addr :=
            hsel.2.2.2.2.1 addr (by
              dsimp only [wsSize, candPredBase, candCostBase, frameParentBase, frameBase]
                at haddr ⊢
              omega)
          unfold forwardStep
          dsimp only [ca]
          simp only [client_simps, ↓reduceIte]
          split_ifs with hfeas0 hx0_eq
          · simpa [client_simps, sSel, selArgs] using hsSel_addr
          · have hcp_mod := hcp_parent.2.2.2.2.1
            dsimp only [fcArgs, sSel, selArgs] at hsFc_eq hcp_mod hsSel_addr ⊢
            rw [hsFc_eq, hcp_mod addr (by dsimp only [wsSize, curParentBase] at haddr ⊢; omega)]
            exact hsSel_addr
          · have hfc_res := hfc.2.2.2.2
            dsimp only [fcArgs, sSel, selArgs] at hsFc_eq hfc_res hx0_eq hsSel_addr ⊢
            rw [hsFc_eq, hfc_res]
            rw [hfc_res] at hx0_eq
            cases hcyc_case : findCycleTable r sel.parents with
            | none => simp [hcyc_case, optFinIdx] at hx0_eq
            | some x0 =>
              simp only [optFinIdx]
              have hcrb_mod := (hcrb_at x0).2.2.2.2.1
              dsimp only [sSel, selArgs] at hcrb_mod
              rw [hcrb_mod addr (by
                dsimp only [wsSize, frameMaskBase, frameBase] at haddr ⊢; omega)]
              exact hsSel_addr
        · unfold forwardStep
          dsimp only [ca]
          simp only [client_simps, ↓reduceIte]
          have hsel_res := hsel.2.2.2.2.2.1
          dsimp only [selArgs, sel] at hsel_res
          rw [hsel_res]
          cases hfeas_b : (selectParents a_k cRed r).feasible
          · dsimp only [sSel, selArgs] at hsSel_fr
            simp only [Bool.false_eq_true, ↓reduceIte, client_simps]
            refine ⟨trivial, hsSel_fr, Or.inr (Or.inr ⟨trivial, ?_⟩)⟩
            rw [heq_aux, hfuel_eq]
            simp [edmondsTableAux, ← hsel_eq_unred, hfeas_b]
          · simp only [↓reduceIte, Nat.one_ne_zero]
            have hfc_res := hfc.2.2.2.2
            dsimp only [fcArgs, sSel, selArgs, sel] at hsFc_eq hfc_res ⊢
            rw [hsFc_eq, hfc_res]
            cases hcyc_case : findCycleTable r (selectParents a_k cRed r).parents with
            | none =>
              simp only [optFinIdx, ↓reduceIte]
              have hcp := hcp_parent
              dsimp only [sSel, selArgs, sel] at hcp hsSel_fr
              refine ⟨trivial, hcp.2.2.2.1.trans hsSel_fr, Or.inr (Or.inl ⟨trivial, by omega,
                frs, (selectParents a_k cRed r).parents, hlen, ?_, ?_, ?_⟩)⟩
              · rw [heq_aux, hfuel_eq]
                simp [edmondsTableAux, ← hsel_eq_unred, hfeas_b, hcyc_case]
              · intro v
                rw [show curParentBase ws n + v.1 =
                  (⟨frameParentBase ws n k, curParentBase ws n, n⟩ : CopyArgs).dst + v.1 from rfl,
                  hcp.2.2.2.2.2 v.1 v.isLt]
                exact hsel.2.2.2.2.2.2 v
              · intro j hj
                exact frameStored_congr (hfrs_sel j hj) fun addr hlo hhi =>
                  hcp.2.2.2.2.1 addr (by dsimp only [curParentBase, frameBase] at hlo ⊢; omega)
            | some x0 =>
              have hx0_ne : x0.1 ≠ n := ne_of_lt x0.isLt
              simp only [optFinIdx, hx0_ne, ↓reduceIte, client_simps]
              have hcrb := hcrb_at x0
              dsimp only [sSel, selArgs, sel] at hcrb
              obtain ⟨hpot', heq_aux', hbnd'⟩ :=
                forwardStep_contract_math hk hpot heq_aux hfeas_b hcyc_case hbnd_k
              refine ⟨trivial, hcrb.2.2.2.1.trans hsSel_fr, Or.inl ⟨trivial, trivial,
                _, _, _, _, by simp [hlen], hpot', heq_aux', hcrb.2.2.2.2.2.1,
                hcrb.2.2.2.2.2.2.1, hbnd', ?_⟩⟩
              intro j hj
              rw [List.length_append, List.length_singleton] at hj
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
              · rw [List.getElem_append_left hlt]
                have hjk : j < k := hlen ▸ hlt
                have hmul : j * (4 * n + 1) + (4 * n + 1) ≤ k * (4 * n + 1) := by
                  simpa [Nat.succ_mul] using Nat.mul_le_mul_right (4 * n + 1) hjk
                exact frameStored_congr (hfrs_sel j hlt) fun addr hlo hhi =>
                  hcrb.2.2.2.2.1 addr (by
                    dsimp only [frameMaskBase, frameBase] at hlo hhi ⊢; omega)
              · simp only [List.getElem_append_right (le_refl frs.length), Nat.sub_self,
                  List.getElem_singleton]
                rw [hlen]
                exact hcrb.2.2.2.2.2.2.2
      · subst status
        refine ⟨by dsimp only [ForwardStepSafe, ca]; exact ⟨hk, hws, fun h => by cases h⟩,
          ?_, ?_,
          by simp [forwardStep, client_simps],
          fun _ _ => by simp [forwardStep, client_simps],
          ?_⟩
        · unfold forwardStep
          simp only [Nat.one_ne_zero, ↓reduceIte]
          exact validHistory_read_bind hf_s_pos (validHistory_pure w _ _)
        · unfold forwardStep
          simp only [Nat.one_ne_zero, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_read]
          simp only [client_simps]
          omega
        · unfold forwardStep
          simp only [Nat.one_ne_zero, ↓reduceIte, client_simps]
          exact ⟨trivial, hfr, Or.inr (Or.inl ⟨trivial, by omega, frs, q₀, hlen, heq_aux,
            hcur_k, hfrs_k⟩)⟩
      · subst status
        refine ⟨by dsimp only [ForwardStepSafe, ca]; exact ⟨hk, hws, fun h => by cases h⟩,
          ?_, ?_,
          by simp [forwardStep, client_simps],
          fun _ _ => by simp [forwardStep, client_simps],
          ?_⟩
        · unfold forwardStep
          simp only [show (2 : ℕ) ≠ 0 by decide, ↓reduceIte]
          exact validHistory_read_bind hf_s_pos (validHistory_pure w _ _)
        · unfold forwardStep
          simp only [show (2 : ℕ) ≠ 0 by decide, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_read]
          simp only [client_simps]
          omega
        · unfold forwardStep
          simp only [show (2 : ℕ) ≠ 0 by decide, ↓reduceIte, client_simps]
          exact ⟨trivial, hfr, Or.inr (Or.inr ⟨trivial, heq_none⟩)⟩)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl ⟨rfl, rfl, a₀, c₀, c₀, [], rfl,
      ⟨fun _ => 0, fun _ _ _ => by simp⟩,
      by simp [expandFrames], ha₀, hc₀,
      fun u col => by have := hB₀ u col; omega,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hcases⟩ := h
  unfold forwardProg
  refine ⟨hsafe, hvh, hmc, hfr_e, hmod_e, ?_⟩
  rcases hcases with ⟨hst0, _, a_n, cUnred, cRed, frs, _, _, heq_aux, _⟩ | hst1 | ⟨hst2, hnone⟩
  · refine Or.inr ⟨by dsimp only [ca] at hst0 ⊢; omega, ?_⟩
    simpa [Nat.sub_self, edmondsTableAux] using heq_aux
  · exact Or.inl hst1
  · exact Or.inr ⟨by dsimp only [ca] at hst2 ⊢; omega, hnone⟩

private theorem edmondsCoreProg_spec {w n ws M₀ : ℕ} (r : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hwb : Fits w (wordBound n M₀))
    (ha₀ : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0)
    (hc₀ : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1])
    (hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀) :
    let ca : CoreArgs := ⟨n, r.1, ws⟩
    let res := (Memory.spec 0).clientResult s₀ (forwardProg ca)
    let s1 := (Memory.spec 0).clientState s₀ (forwardProg ca)
    let s' := (Memory.spec 0).clientState s₀ (edmondsCoreProg ca)
    let status := (Memory.spec 0).clientResult s₀ (edmondsCoreProg ca)
    (Fits w 1 ∧
      iterationSafe forwardStep ForwardStepSafe w ca n ⟨0, 0, 0⟩ s₀ ∧
      (res.status = 1 →
        iterationSafe backwardStep BackwardStepSafe w ⟨n, ws, res.depth⟩ res.depth 0 s1)) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsCoreProg ca)) ∧
      memoryCost (edmondsCoreProg ca) s₀ ≤ 43 * n ^ 3 + 18 * n ^ 2 + 6 * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + wsSize n) → s'.mem addr = s₀.mem addr) ∧
      match edmondsTableAux r n a₀ c₀ with
      | some p =>
        status = 1 ∧ ∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (p[v.1]).1
      | none =>
        status = 0 := by
  let ca : CoreArgs := ⟨n, r.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfwd := forwardProg_spec r a₀ c₀ s₀ hws hf hwb ha₀ hc₀ hB₀
  set res := (Memory.spec 0).clientResult s₀ (forwardProg ⟨n, r.1, ws⟩)
  set s1 := (Memory.spec 0).clientState s₀ (forwardProg ⟨n, r.1, ws⟩)
  have hf_s1 : ws + wsSize n ≤ s1.frontier := by rw [hfwd.2.2.2.1]; exact hf
  rcases hfwd.2.2.2.2.2 with ⟨hst1, hdep_le, frs, q₀, hlen, heq_some, hcur1, hfrs1⟩ |
      ⟨hst_ne, heq_none⟩
  · have hbwd := backwardProg_spec r.pos frs q₀ s1 hdep_le hlen hws hf_s1 hcur1 hfrs1
    unfold edmondsCoreProg
    dsimp only [ca]
    refine ⟨⟨h1, hfwd.1, fun _ => hbwd.1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hfwd.2.1 ?_
      change (Memory.spec w).ValidHistory s1
        ((Memory.spec w).clientHistory s1
          (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1 else pure 0))
      rw [ite_eq_left hst1]
      exact validHistory_bind_step hbwd.2.1 (validHistory_pure w _ _)
    · rw [memoryCost_bind']
      change memoryCost (forwardProg ⟨n, r.1, ws⟩) s₀ +
        memoryCost (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1
          else pure 0) s1 ≤ _
      rw [ite_eq_left hst1]
      simp only [memoryCost_bind', client_simps]
      have cf := hfwd.2.2.1
      have cb := hbwd.2.2.1
      have hcb_n : (7 * n + 4) * res.depth ≤ (7 * n + 4) * n := Nat.mul_le_mul_left _ hdep_le
      have hid : (43 * (n * n) + 11 * n + 2) * n + (7 * n + 4) * n =
          43 * n ^ 3 + 18 * n ^ 2 + 6 * n := by ring
      linarith only [cf, cb, hcb_n, hid]
    · simp only [client_simps, hst1, ↓reduceIte]
      exact hbwd.2.2.2.1.trans hfwd.2.2.2.1
    · intro addr haddr
      simp only [client_simps, hst1, ↓reduceIte]
      rw [hbwd.2.2.2.2.1 addr (by
        dsimp only [wsSize, curParentBase, nextParentBase] at haddr ⊢; omega)]
      exact hfwd.2.2.2.2.1 addr haddr
    · rw [heq_some]
      simp only [client_simps, hst1, ↓reduceIte]
      exact ⟨trivial, hbwd.2.2.2.2.2⟩
  · unfold edmondsCoreProg
    dsimp only [ca]
    refine ⟨⟨h1, hfwd.1, fun h => absurd h hst_ne⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hfwd.2.1 ?_
      change (Memory.spec w).ValidHistory s1
        ((Memory.spec w).clientHistory s1
          (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1 else pure 0))
      rw [ite_eq_right hst_ne]
      exact validHistory_pure w _ _
    · rw [memoryCost_bind']
      change memoryCost (forwardProg ⟨n, r.1, ws⟩) s₀ +
        memoryCost (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1
          else pure 0) s1 ≤ _
      rw [ite_eq_right hst_ne]
      simp only [client_simps]
      have cf := hfwd.2.2.1
      have hnn := Nat.zero_le ((7 * n + 4) * n)
      have hid : (43 * (n * n) + 11 * n + 2) * n + (7 * n + 4) * n =
          43 * n ^ 3 + 18 * n ^ 2 + 6 * n := by ring
      linarith only [cf, hid, hnn]
    · simp only [client_simps, hst_ne, ↓reduceIte]
      exact hfwd.2.2.2.1
    · intro addr haddr
      simp only [client_simps, hst_ne, ↓reduceIte]
      exact hfwd.2.2.2.2.1 addr haddr
    · rw [heq_none]
      simp [client_simps, hst_ne]

/-! ### `FinEnum` bridges and flat input encodings -/

private theorem finEnum_equiv_val {n : ℕ} (v : Fin n) :
    ((@FinEnum.equiv (Fin n) FinEnum.fin) v).1 = v.1 := by
  change ((List.finRange n).dedup).idxOf v = v.1
  rw [(List.nodup_finRange n).dedup, List.idxOf_finRange]

private theorem finEnum_equiv_symm_val {n : ℕ} (i : Fin (FinEnum.card (Fin n))) :
    ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i).1 = i.1 := by
  have h := finEnum_equiv_val ((@FinEnum.equiv (Fin n) FinEnum.fin).symm i)
  simpa using h.symm

private theorem edmondsTableAux_congr_dim {n₁ n₂ : ℕ} (hn : n₁ = n₂)
    (r₁ : Fin n₁) (r₂ : Fin n₂) (hr : r₁.1 = r₂.1)
    (fuel : ℕ) (a₁ : AdjTable n₁) (a₂ : AdjTable n₂)
    (c₁ : CostTable ℤ n₁) (c₂ : CostTable ℤ n₂)
    (ha : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      a₁[i][j] = a₂[i][j])
    (hc : ∀ i j, (hi₁ : i < n₁) → (hj₁ : j < n₁) → (hi₂ : i < n₂) → (hj₂ : j < n₂) →
      c₁[i][j] = c₂[i][j]) :
    (edmondsTableAux r₁ fuel a₁ c₁).map (fun p => (List.finRange n₁).map fun v => (p[v.1]).1) =
      (edmondsTableAux r₂ fuel a₂ c₂).map
        (fun p => (List.finRange n₂).map fun v => (p[v.1]).1) := by
  subst hn
  have hrr : r₁ = r₂ := Fin.ext hr
  subst hrr
  have ha_eq : a₁ = a₂ := Vector.ext fun i hi => Vector.ext fun j hj => ha i j hi hj hi hj
  have hc_eq : c₁ = c₂ := Vector.ext fun i hi => Vector.ext fun j hj => hc i j hi hj hi hj
  subst ha_eq hc_eq
  rfl

private theorem edmonds_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmonds G c r).map (fun f => (List.finRange n).map fun v => (f v).1) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj u w))
        (initCostTable n c)).map
        (fun p => (List.finRange n).map fun v => (p[v.1]).1) := by
  rw [← edmondsTable_eq_edmonds]
  unfold edmondsTable
  rw [Option.map_map]
  let e : Fin n ≃ Fin (FinEnum.card (Fin n)) := @FinEnum.equiv (Fin n) FinEnum.fin
  have hcard : FinEnum.card (Fin n) = n := FinEnum.card_fin
  let A₁ := initAdjTable (FinEnum.card (Fin n)) fun u w => decide (G.Adj (e.symm u) (e.symm w))
  let C₁ := initCostTable (FinEnum.card (Fin n)) fun u w => c (e.symm u) (e.symm w)
  have hmap_fn : ∀ p : ParentTable (FinEnum.card (Fin n)),
      ((List.finRange n).map fun v => (e.symm p[(e v).1]).1) =
        ((List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.1]).1) := fun p => by
    refine List.ext_getElem (by simp [hcard]) fun k hk₁ hk₂ => ?_
    simp only [List.getElem_map, List.getElem_finRange]
    have hk_n : k < n := by simpa using hk₁
    rw [finEnum_equiv_symm_val]
    have hek : (e ⟨k, hk_n⟩).1 = k := finEnum_equiv_val ⟨k, hk_n⟩
    simp [hek]
  have hfuel : edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁ =
      edmondsTableAux (e r) n A₁ C₁ := congrArg (fun k => edmondsTableAux (e r) k A₁ C₁) hcard
  have step1 : Option.map (fun p => (List.finRange n).map fun v => (e.symm p[(e v).1]).1)
      (edmondsTableAux (e r) (FinEnum.card (Fin n)) A₁ C₁) =
      Option.map (fun p => (List.finRange (FinEnum.card (Fin n))).map fun u => (p[u.1]).1)
        (edmondsTableAux (e r) n A₁ C₁) := by
    rw [hfuel]
    exact congrArg (Option.map · _) (funext hmap_fn)
  refine step1.trans
    (edmondsTableAux_congr_dim hcard (e r) r (finEnum_equiv_val r) n A₁ _ C₁ _ ?_ ?_)
  · intro i j hi₁ hj₁ hi₂ hj₂
    have h1 : A₁[i][j] = decide (G.Adj (e.symm ⟨i, hi₁⟩) (e.symm ⟨j, hj₁⟩)) :=
      getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
    have h2 : (initAdjTable n fun u w => decide (G.Adj u w))[i][j] =
        decide (G.Adj ⟨i, hi₂⟩ ⟨j, hj₂⟩) :=
      getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
    have hu : e.symm ⟨i, hi₁⟩ = ⟨i, hi₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨i, hi₁⟩)
    have hw : e.symm ⟨j, hj₁⟩ = ⟨j, hj₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨j, hj₁⟩)
    rw [h1, h2, hu, hw]
  · intro i j hi₁ hj₁ hi₂ hj₂
    have h1 : C₁[i][j] = c (e.symm ⟨i, hi₁⟩) (e.symm ⟨j, hj₁⟩) :=
      getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
    have h2 : (initCostTable n c)[i][j] = c ⟨i, hi₂⟩ ⟨j, hj₂⟩ :=
      getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
    have hu : e.symm ⟨i, hi₁⟩ = ⟨i, hi₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨i, hi₁⟩)
    have hw : e.symm ⟨j, hj₁⟩ = ⟨j, hj₂⟩ := Fin.ext (finEnum_equiv_symm_val ⟨j, hj₁⟩)
    rw [h1, h2, hu, hw]

private theorem edmondsOut_fin_map_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Fin n → ℤ) (r : Fin n) :
    (edmondsOut G c r).map (fun f => (List.finRange n).map fun v => (f v).1) =
      (edmondsTableAux r n
        (initAdjTable n fun u w => decide (G.Adj w u))
        (initCostTable n fun u w => c w u)).map
        (fun p => (List.finRange n).map fun v => (p[v.1]).1) := by
  have hout : edmondsOut G c r = edmonds G.reverse (fun u w => c w u) r := by
    rw [← edmondsOutTable_eq_edmondsOut, ← edmondsTable_eq_edmonds]
    rfl
  rw [hout]
  exact edmonds_fin_map_eq G.reverse (fun u w => c w u) r

private def superRootAdjFin {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    AdjTable (n + 1) :=
  initAdjTable (n + 1) fun x y =>
    if hx : x.1 < n then
      if hy : y.1 < n then decide (G.Adj ⟨y.1, hy⟩ ⟨x.1, hx⟩)
      else true
    else false

private def superRootCostFin {n : ℕ} (wt : Fin n → Fin n → ℤ) : CostTable ℤ (n + 1) :=
  initCostTable (n + 1) fun x y =>
    if hx : x.1 < n then
      if hy : y.1 < n then -wt ⟨y.1, hy⟩ ⟨x.1, hx⟩
      else 0
    else 0

private theorem optimumBranchingParent_fin_eq {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (wt : Fin n → Fin n → ℤ) :
    ∃ p : ParentTable (n + 1),
      edmondsTableAux (Fin.last n) (n + 1) (superRootAdjFin G) (superRootCostFin wt) = some p ∧
      ∀ v : Fin n, (optimumBranchingParent G wt v).1 =
        if (p[v.1]).1 < n then (p[v.1]).1 else v.1 := by
  let _ : FinEnum (Option (Fin n)) := optionFinEnum (Fin n)
  have hcard_fin : @FinEnum.card (Fin n) FinEnum.fin = n := FinEnum.card_fin
  have hcard_opt : FinEnum.card (Option (Fin n)) = n + 1 := by
    change @FinEnum.card (Fin n) FinEnum.fin + 1 = n + 1
    omega
  let eOpt : Option (Fin n) ≃ Fin (FinEnum.card (Option (Fin n))) := FinEnum.equiv
  have he_none : (eOpt none).1 = n := hcard_fin
  have he_some (v : Fin n) : (eOpt (some v)).1 = v.1 := finEnum_equiv_val v
  have hsymm_lt (i : Fin (FinEnum.card (Option (Fin n)))) (hi : i.1 < n) :
      eOpt.symm i = some ⟨i.1, hi⟩ := by
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (he_some ⟨i.1, hi⟩).symm
  have hsymm_eq (i : Fin (FinEnum.card (Option (Fin n)))) (hi : ¬i.1 < n) :
      eOpt.symm i = none := by
    have hin : i.1 = n := by have := i.isLt; omega
    apply eOpt.injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (hin.trans he_none.symm)
  obtain ⟨pOpt, hpOpt⟩ := edmonds_superRootDigraph_isSome G wt
  have hparent_eq : optimumBranchingParent G wt = restrictParent pOpt := by
    simp [optimumBranchingParent, hpOpt]
  have htab_eq := edmondsTable_eq_edmonds G.superRootDigraph (superRootCost wt) none
  rw [hpOpt] at htab_eq
  unfold edmondsTable at htab_eq
  change Option.map (fun p v => eOpt.symm p[(eOpt v).1])
    (edmondsTableAux (eOpt none) (FinEnum.card (Option (Fin n)))
      (initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
        decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w)))
      (initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
        superRootCost wt (eOpt.symm u) (eOpt.symm w))) = some pOpt at htab_eq
  cases haux1 : edmondsTableAux (eOpt none) (FinEnum.card (Option (Fin n)))
      (initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
        decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w)))
      (initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
        superRootCost wt (eOpt.symm u) (eOpt.symm w)) with
  | none =>
    rw [haux1] at htab_eq
    cases htab_eq
  | some p1 =>
    rw [haux1, Option.map_some, Option.some.injEq] at htab_eq
    let A₁ := initAdjTable (FinEnum.card (Option (Fin n))) fun u w =>
      decide (G.superRootDigraph.Adj (eOpt.symm u) (eOpt.symm w))
    let C₁ := initCostTable (FinEnum.card (Option (Fin n))) fun u w =>
      superRootCost wt (eOpt.symm u) (eOpt.symm w)
    have hcongr := edmondsTableAux_congr_dim hcard_opt (eOpt none) (Fin.last n) he_none (n + 1)
      A₁ (superRootAdjFin G) C₁ (superRootCostFin wt)
      (fun i j hi₁ hj₁ hi₂ hj₂ => by
        have h1 : A₁[i][j] =
            decide (G.superRootDigraph.Adj (eOpt.symm ⟨i, hi₁⟩) (eOpt.symm ⟨j, hj₁⟩)) :=
          getElem_initAdjTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
        have h2 : (superRootAdjFin G)[i][j] =
            if hx : i < n then if hy : j < n then decide (G.Adj ⟨j, hy⟩ ⟨i, hx⟩) else true
            else false :=
          getElem_initAdjTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
        rw [h1, h2]
        by_cases hi : i < n
        · rw [hsymm_lt ⟨i, hi₁⟩ hi]
          by_cases hj : j < n
          · rw [hsymm_lt ⟨j, hj₁⟩ hj]; simp [hi, hj]
          · rw [hsymm_eq ⟨j, hj₁⟩ hj]; simp [hi, hj]
        · rw [hsymm_eq ⟨i, hi₁⟩ hi]; simp [hi])
      (fun i j hi₁ hj₁ hi₂ hj₂ => by
        have h1 : C₁[i][j] = superRootCost wt (eOpt.symm ⟨i, hi₁⟩) (eOpt.symm ⟨j, hj₁⟩) :=
          getElem_initCostTable _ _ ⟨i, hi₁⟩ ⟨j, hj₁⟩
        have h2 : (superRootCostFin wt)[i][j] =
            if hx : i < n then if hy : j < n then -wt ⟨j, hy⟩ ⟨i, hx⟩ else 0 else 0 :=
          getElem_initCostTable _ _ ⟨i, hi₂⟩ ⟨j, hj₂⟩
        rw [h1, h2]
        by_cases hi : i < n
        · rw [hsymm_lt ⟨i, hi₁⟩ hi]
          by_cases hj : j < n
          · rw [hsymm_lt ⟨j, hj₁⟩ hj]; simp [hi, hj, superRootCost]
          · rw [hsymm_eq ⟨j, hj₁⟩ hj]; simp [hi, hj, superRootCost]
        · rw [hsymm_eq ⟨i, hi₁⟩ hi]; simp [hi, superRootCost])
    have haux1' : edmondsTableAux (eOpt none) (n + 1) A₁ C₁ = some p1 := by
      rw [← hcard_opt]
      exact haux1
    rw [haux1', Option.map_some] at hcongr
    cases haux2 : edmondsTableAux (Fin.last n) (n + 1) (superRootAdjFin G) (superRootCostFin wt)
    with
    | none => simp [haux2] at hcongr
    | some p2 =>
      simp only [haux2, Option.map_some, Option.some.injEq] at hcongr
      refine ⟨p2, rfl, fun v => ?_⟩
      have hv_eq : (p1[v.1]'(by omega)).1 = (p2[v.1]'(by omega)).1 := by
        have hget := congrArg (fun l => l.getD v.1 0) hcongr
        have hl1 : v.1 < ((List.finRange (FinEnum.card (Option (Fin n)))).map
            fun u => (p1[u.1]).1).length := by simp [hcard_opt]
        have hl2 : v.1 < ((List.finRange (n + 1)).map fun u => (p2[u.1]).1).length := by simp
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1, Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl2, Option.getD_some] at hget
        simpa using hget
      have hp_v : pOpt (some v) = eOpt.symm (p1[(eOpt (some v)).1]) :=
        (congrFun htab_eq (some v)).symm
      rw [hparent_eq]
      unfold restrictParent
      rw [hp_v]
      have hev : (eOpt (some v)).1 = v.1 := he_some v
      have hp1_eq : p1[(eOpt (some v)).1] = p1[v.1]'(by omega) := by simp [hev]
      rw [hp1_eq]
      by_cases hlt : (p2[v.1]'(by omega)).1 < n
      · have hlt1 : (p1[v.1]'(by omega)).1 < n := hv_eq ▸ hlt
        rw [hsymm_lt _ hlt1]
        simp [hlt, hv_eq]
      · have hlt1 : ¬(p1[v.1]'(by omega)).1 < n := hv_eq ▸ hlt
        rw [hsymm_eq _ hlt1]
        simp [hlt]

public section

/-- Row-major `n × n` Boolean matrix flattened to `0`/`1` words. -/
@[expose] def flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => if a u v then 1 else 0

/-- Row-major `n × n` signed integer matrix flattened via `Signed.encode`. -/
@[expose] def flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => Signed.encode (c u v)

@[simp] theorem length_flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) :
    (flattenBoolMatrix n a).length = n * n := by
  unfold flattenBoolMatrix
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

@[simp] theorem length_flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) :
    (flattenSignedMatrix n c).length = n * n := by
  unfold flattenSignedMatrix
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

theorem getD_flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) (u v : Fin n) :
    (flattenBoolMatrix n a).getD (u.1 * n + v.1) 0 = if a u v then 1 else 0 := by
  simpa only [flattenBoolMatrix, ← List.ofFn_eq_map] using
    List.getD_flatMap_ofFn (fun x y => if a x y then 1 else 0) 0 u v

theorem getD_flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) (u v : Fin n) :
    (flattenSignedMatrix n c).getD (u.1 * n + v.1) 0 = Signed.encode (c u v) := by
  simpa only [flattenSignedMatrix, ← List.ofFn_eq_map] using
    List.getD_flatMap_ofFn (fun x y => Signed.encode (c x y)) 0 u v

/-- Rooted weighted digraph input on `Fin n` for Word-RAM Chu–Liu/Edmonds solvers. -/
structure ArborescenceInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- Designated root vertex. -/
  root : Fin n
  /-- Boolean adjacency matrix (`adj u v = true` iff arc `u → v` is present). -/
  adj : Fin n → Fin n → Bool
  /-- Signed integer arc costs. -/
  cost : Fin n → Fin n → ℤ

/-- Underlying `Digraph (Fin I.n)` of an `ArborescenceInput`. -/
@[expose] def ArborescenceInput.digraph (I : ArborescenceInput) : Digraph (Fin I.n) where
  Adj u v := I.adj u v = true

instance (I : ArborescenceInput) : DecidableRel I.digraph.Adj :=
  fun u v => inferInstanceAs (Decidable (I.adj u v = true))

/-- Maximum absolute arc cost `max_{u, v} |I.cost u v|`. -/
@[expose] def ArborescenceInput.maxAbsCost (I : ArborescenceInput) : ℕ :=
  Finset.univ.sup fun p : Fin I.n × Fin I.n => (I.cost p.1 p.2).natAbs

theorem ArborescenceInput.natAbs_cost_le_maxAbsCost (I : ArborescenceInput) (u v : Fin I.n) :
    (I.cost u v).natAbs ≤ I.maxAbsCost :=
  Finset.le_sup (f := fun p : Fin I.n × Fin I.n => (I.cost p.1 p.2).natAbs)
    (Finset.mem_univ (u, v))

/-- Intrinsic polynomial word-value/address bound `wordBound I.n I.maxAbsCost`
(`Fits w I.wordBound` means `I.wordBound < 2 ^ w`, so `w` of order
`log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
@[expose] def ArborescenceInput.wordBound (I : ArborescenceInput) : ℕ :=
  Arborescence.wordBound I.n I.maxAbsCost

/-- Flat Word-RAM input word list `[n, root] ++ flattenBoolMatrix ++ flattenSignedMatrix`. -/
@[expose] def ArborescenceInput.encode (I : ArborescenceInput) : List ℕ :=
  I.n :: I.root.1 :: (flattenBoolMatrix I.n I.adj ++ flattenSignedMatrix I.n I.cost)

/-- Expected list output for minimum-cost spanning in-arborescence (`[]` when infeasible, or the
length-`n` parent list `[p(0), …, p(n - 1)]` when `edmonds I.digraph I.cost I.root = some p`). -/
@[expose] def ArborescenceInput.expectedParentList (I : ArborescenceInput) : List ℕ :=
  match edmonds I.digraph I.cost I.root with
  | some p => (List.finRange I.n).map fun v => (p v).1
  | none => []

/-- `I.expectedParentList` is empty iff `I.digraph` has no spanning in-arborescence rooted at
`I.root`. -/
theorem ArborescenceInput.expectedParentList_eq_nil_iff (I : ArborescenceInput) :
    I.expectedParentList = [] ↔ ∀ t, ¬ IsInArborescenceParent I.digraph.Adj I.root t := by
  unfold ArborescenceInput.expectedParentList
  cases h : edmonds I.digraph I.cost I.root with
  | none =>
    simp only [true_iff]
    exact edmonds_eq_none_iff.mp h
  | some p =>
    have hne : ((List.finRange I.n).map fun v => (p v).1) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_map, List.length_finRange, List.length_nil] at hlen
      exact Nat.ne_of_gt I.root.pos hlen
    refine ⟨fun hnil => absurd hnil hne, fun hall => ?_⟩
    exact absurd (edmonds_spec.1 p h).1 (hall p)

/-- Whenever `I.expectedParentList` is nonempty, it encodes the parent map of a minimum-cost
spanning in-arborescence of `I.digraph` rooted at `I.root`. -/
theorem ArborescenceInput.expectedParentList_spec (I : ArborescenceInput)
    (hne : I.expectedParentList ≠ []) :
    ∃ p : Fin I.n → Fin I.n,
      I.expectedParentList = (List.finRange I.n).map (fun v => (p v).1) ∧
      (Digraph.parentDigraph I.root p).IsInArborescence I.root ∧
      Digraph.parentDigraph I.root p ≤ I.digraph ∧
      ∀ (T : Digraph (Fin I.n)) [DecidableRel T.Adj],
        T.IsInArborescence I.root → T ≤ I.digraph →
        arcCost (Digraph.parentDigraph I.root p) I.cost ≤ arcCost T I.cost := by
  unfold ArborescenceInput.expectedParentList at hne ⊢
  cases h : edmonds I.digraph I.cost I.root with
  | none => simp [h] at hne
  | some p =>
    obtain ⟨h1, h2, h3⟩ := edmonds_optimal h
    refine ⟨p, rfl, h1, h2, fun T _ hT hTG => ?_⟩
    convert h3 T hT hTG

/-- Expected list output for minimum-cost spanning out-arborescence (`[]` when infeasible, or the
length-`n` parent list `[p(0), …, p(n - 1)]` when `edmondsOut I.digraph I.cost I.root = some p`). -/
@[expose] def ArborescenceInput.expectedOutParentList (I : ArborescenceInput) : List ℕ :=
  match edmondsOut I.digraph I.cost I.root with
  | some p => (List.finRange I.n).map fun v => (p v).1
  | none => []

/-- `I.expectedOutParentList` is empty iff `I.digraph` has no spanning out-arborescence rooted at
`I.root`. -/
theorem ArborescenceInput.expectedOutParentList_eq_nil_iff (I : ArborescenceInput) :
    I.expectedOutParentList = [] ↔
      ∀ t, ¬ IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root t := by
  unfold ArborescenceInput.expectedOutParentList
  cases h : edmondsOut I.digraph I.cost I.root with
  | none =>
    simp only [true_iff]
    exact edmondsOut_spec.2 h
  | some p =>
    have hne : ((List.finRange I.n).map fun v => (p v).1) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_map, List.length_finRange, List.length_nil] at hlen
      exact Nat.ne_of_gt I.root.pos hlen
    refine ⟨fun hnil => absurd hnil hne, fun hall => ?_⟩
    exact absurd (edmondsOut_spec.1 p h).1 (hall p)

/-- Whenever `I.expectedOutParentList` is nonempty, it encodes the parent map of a minimum-cost
spanning out-arborescence of `I.digraph` rooted at `I.root`. -/
theorem ArborescenceInput.expectedOutParentList_spec (I : ArborescenceInput)
    (hne : I.expectedOutParentList ≠ []) :
    ∃ p : Fin I.n → Fin I.n,
      I.expectedOutParentList = (List.finRange I.n).map (fun v => (p v).1) ∧
      IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root p ∧
      ∀ t, IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root t →
        parentCost (fun u w => I.cost w u) I.root p ≤
          parentCost (fun u w => I.cost w u) I.root t := by
  unfold ArborescenceInput.expectedOutParentList at hne ⊢
  cases h : edmondsOut I.digraph I.cost I.root with
  | none => simp [h] at hne
  | some p =>
    obtain ⟨h1, h2⟩ := edmondsOut_spec.1 p h
    refine ⟨p, rfl, h1, fun t ht => ?_⟩
    convert h2 t ht

/-- Weighted digraph input on `Fin n` for Word-RAM maximum-weight branching. -/
structure BranchingInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- Boolean adjacency matrix (`adj u v = true` iff arc `u → v` is present). -/
  adj : Fin n → Fin n → Bool
  /-- Signed integer arc weights. -/
  weight : Fin n → Fin n → ℤ

/-- Underlying `Digraph (Fin I.n)` of a `BranchingInput`. -/
@[expose] def BranchingInput.digraph (I : BranchingInput) : Digraph (Fin I.n) where
  Adj u v := I.adj u v = true

instance (I : BranchingInput) : DecidableRel I.digraph.Adj :=
  fun u v => inferInstanceAs (Decidable (I.adj u v = true))

/-- Maximum absolute arc weight `max_{u, v} |I.weight u v|` (`0` when `n = 0`). -/
@[expose] def BranchingInput.maxAbsWeight (I : BranchingInput) : ℕ :=
  Finset.univ.sup fun p : Fin I.n × Fin I.n => (I.weight p.1 p.2).natAbs

theorem BranchingInput.natAbs_weight_le_maxAbsWeight (I : BranchingInput) (u v : Fin I.n) :
    (I.weight u v).natAbs ≤ I.maxAbsWeight :=
  Finset.le_sup (f := fun p : Fin I.n × Fin I.n => (I.weight p.1 p.2).natAbs)
    (Finset.mem_univ (u, v))

/-- Intrinsic polynomial word-value/address bound `wordBound (I.n + 1) I.maxAbsWeight`
(`Fits w I.wordBound` means `I.wordBound < 2 ^ w`, so `w` of order
`log(I.n + 2) + log(I.maxAbsWeight + 2)` bits suffices). -/
@[expose] def BranchingInput.wordBound (I : BranchingInput) : ℕ :=
  Arborescence.wordBound (I.n + 1) I.maxAbsWeight

/-- Flat Word-RAM input word list `[n] ++ flattenBoolMatrix ++ flattenSignedMatrix`. -/
@[expose] def BranchingInput.encode (I : BranchingInput) : List ℕ :=
  I.n :: (flattenBoolMatrix I.n I.adj ++ flattenSignedMatrix I.n I.weight)

/-- Expected length-`n` parent list `[p(0), …, p(n - 1)]` of `optimumBranchingParent`. -/
@[expose] def BranchingInput.expectedParentList (I : BranchingInput) : List ℕ :=
  (List.finRange I.n).map fun v => (optimumBranchingParent I.digraph I.weight v).1

/-- `I.expectedParentList` encodes `optimumBranchingParent I.digraph I.weight`, whose branching
digraph `optimumBranching I.digraph I.weight` is a maximum-weight branching of `I.digraph`. -/
theorem BranchingInput.expectedParentList_spec (I : BranchingInput) :
    I.expectedParentList =
      (List.finRange I.n).map (fun v => (optimumBranchingParent I.digraph I.weight v).1) ∧
    (optimumBranching I.digraph I.weight).IsBranching ∧
    optimumBranching I.digraph I.weight ≤ I.digraph ∧
    ∀ (B : Digraph (Fin I.n)) [DecidableRel B.Adj],
      B.IsBranching → B ≤ I.digraph →
      arcCost B I.weight ≤ arcCost (optimumBranching I.digraph I.weight) I.weight := by
  obtain ⟨h1, h2, h3⟩ := optimumBranching_spec I.digraph I.weight
  refine ⟨rfl, h1, h2, fun B _ hB hBG => ?_⟩
  convert h3 B hB hBG

end

/-! ### Entry programs (`edmondsProg`, `edmondsOutProg`, `optimumBranchingProg`) -/

private theorem init_mem_encode_arb_adj (I : ArborescenceInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (3 + (u.1 * I.n + v.1)) = if I.adj u v then 1 else 0 := by
  rw [show 3 + (u.1 * I.n + v.1) = ((u.1 * I.n + v.1) + 2) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((u.1 * I.n + v.1) + 2) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [ArborescenceInput.encode]
  rw [List.getD_cons_succ, List.getD_cons_succ]
  have hlt : u.1 * I.n + v.1 < (flattenBoolMatrix I.n I.adj).length := by
    rw [length_flattenBoolMatrix]; exact List.mul_add_lt_sq u.isLt v.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  exact getD_flattenBoolMatrix I.n I.adj u v

private theorem init_mem_encode_arb_cost (I : ArborescenceInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (3 + I.n * I.n + (u.1 * I.n + v.1)) =
      Signed.encode (I.cost u v) := by
  rw [show 3 + I.n * I.n + (u.1 * I.n + v.1) =
    ((I.n * I.n + (u.1 * I.n + v.1)) + 2) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((I.n * I.n + (u.1 * I.n + v.1)) + 2) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [ArborescenceInput.encode]
  rw [List.getD_cons_succ, List.getD_cons_succ]
  have hlen1 : (flattenBoolMatrix I.n I.adj).length = I.n * I.n :=
    length_flattenBoolMatrix I.n I.adj
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
  simp only [hlen1, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact getD_flattenSignedMatrix I.n I.cost u v

private theorem fits_mem_flatten_adj_signed {w n m M₀ : ℕ}
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

private theorem inputFits_arb_encode {w M₀ : ℕ} (I : ArborescenceInput)
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

/-- Every word width fitting `I.wordBound` satisfies `InputFits w I.encode`. -/
public theorem ArborescenceInput.inputFits_encode {w : ℕ} (I : ArborescenceInput)
    (hwb : Fits w I.wordBound) : InputFits w I.encode :=
  (inputFits_arb_encode I I.natAbs_cost_le_maxAbsCost hwb).2

private structure FinishArbArgs where
  n : ℕ
  r : ℕ
  ws : ℕ
  outAddr : ℕ

private word_enc_structure encFinishArbArgs : FinishArbArgs where
  n : wordWords, r : wordWords, ws : wordWords, outAddr : wordWords

private instance : WordEncoding FinishArbArgs := ⟨4, encFinishArbArgs⟩

private def finishArbProg (a : FinishArbArgs) : Memory.Prog ℕ := do
  let status ← edmondsCoreProg ⟨a.n, a.r, a.ws⟩
  if status = 1 then
    Memory.write a.outAddr a.n
    let _ ← copyWordsProg ⟨curParentBase a.ws a.n, a.outAddr + 1, a.n⟩
    pure a.outAddr
  else
    Memory.write a.outAddr 0
    pure a.outAddr

private abbrev FinishArbSafe (w : ℕ) (a : FinishArbArgs) (s₃ : Memory.State) : Prop :=
  let ca : CoreArgs := ⟨a.n, a.r, a.ws⟩
  let res := (Memory.spec 0).clientResult s₃ (forwardProg ca)
  let sf := (Memory.spec 0).clientState s₃ (forwardProg ca)
  let status := (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca)
  let s₄ := (Memory.spec 0).clientState s₃ (edmondsCoreProg ca)
  let s₄w : Memory.State := ⟨Function.update s₄.mem a.outAddr a.n, s₄.frontier⟩
  a.outAddr = a.ws + wsSize a.n ∧ Fits w (a.outAddr + (a.n + 1) + 8) ∧
    iterationSafe forwardStep ForwardStepSafe w ca a.n ⟨0, 0, 0⟩ s₃ ∧
    (res.status = 1 →
      iterationSafe backwardStep BackwardStepSafe w ⟨a.n, a.ws, res.depth⟩ res.depth 0 sf) ∧
    (status = 1 →
      iterationSafe copyStep CopyStepSafe w ⟨curParentBase a.ws a.n, a.outAddr + 1, a.n⟩
        a.n 0 s₄w)

private theorem finishArbProg_realizes :
    Realizes .exact finishArbProg encFinishArbArgs wordWords FinishArbSafe (fun _ _ => 0) := by
  unfold finishArbProg
  realize [edmondsCoreProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hout, hfit, hfwd, hbwd, hcpOut⟩ := h
    first
    | exact hfwd
    | exact hbwd
    | exact hcpOut ‹_›
    | exact hfit.of_le (by rw [hout]; dsimp only [wsSize, curParentBase, frameBase]; nlinarith)

private theorem finishArbProg_spec {w n ws M₀ : ℕ} (root : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₃ : Memory.State) (expected : List ℕ)
    (hfit_top : Fits w (ws + wsSize n + (n + 1) + 8))
    (hs₃_fr : s₃.frontier = ws + wsSize n + (n + 1))
    (hwb : Fits w (wordBound n M₀))
    (ha₃ : ∀ u col : Fin n,
      s₃.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0)
    (hc₃ : ∀ u col : Fin n,
      s₃.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1])
    (hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀)
    (hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => expected = (List.finRange n).map fun v => (pTab[v.1]).1
      | none => expected = []) :
    let outAddr := ws + wsSize n
    let fa : FinishArbArgs := ⟨n, root.1, ws, outAddr⟩
    let s' := (Memory.spec 0).clientState s₃ (finishArbProg fa)
    FinishArbSafe w fa s₃ ∧
      (Memory.spec w).ValidHistory s₃ ((Memory.spec w).clientHistory s₃ (finishArbProg fa)) ∧
      memoryCost (finishArbProg fa) s₃ ≤ 43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1 ∧
      (Memory.spec 0).clientResult s₃ (finishArbProg fa) = outAddr ∧
      outputList s'.mem outAddr = expected ∧
      Fits w (outAddr + expected.length) := by
  let outAddr := ws + wsSize n
  let fa : FinishArbArgs := ⟨n, root.1, ws, outAddr⟩
  have hws_fit : WsFits w ws n := hfit_top.of_le (by omega)
  have hcore := edmondsCoreProg_spec root a₀ c₀ s₃ hws_fit
    (by rw [hs₃_fr]; omega) hwb ha₃ hc₃ hB₀
  let ca : CoreArgs := ⟨n, root.1, ws⟩
  let s₄ := (Memory.spec 0).clientState s₃ (edmondsCoreProg ca)
  have hs₄_fr : s₄.frontier = outAddr + (n + 1) := hcore.2.2.2.1.trans hs₃_fr
  cases haux : edmondsTableAux root n a₀ c₀ with
  | some pTab =>
    rw [haux] at hexp
    have hcore_res : (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 ∧
        ∀ v : Fin n, s₄.mem (curParentBase ws n + v.1) = (pTab[v.1]).1 := by
      have h := hcore.2.2.2.2.2
      rwa [haux] at h
    let s₄w : Memory.State := ⟨Function.update s₄.mem outAddr n, s₄.frontier⟩
    let cpOut : CopyArgs := ⟨curParentBase ws n, outAddr + 1, n⟩
    have hcpOut := copyWordsProg_spec cpOut s₄w
      (by dsimp only [cpOut, s₄w]; rw [hs₄_fr]; dsimp only [outAddr, wsSize, curParentBase];
          nlinarith)
      (by dsimp only [cpOut, s₄w]; rw [hs₄_fr]; dsimp only [outAddr]; omega)
      (Or.inl (by dsimp only [cpOut, outAddr, wsSize, curParentBase]; nlinarith))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr, wsSize, curParentBase]; nlinarith))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr]; omega))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr]; omega))
      (fun i hi => by
        dsimp only [cpOut, s₄w]
        rw [Function.update_of_ne (by dsimp only [outAddr, wsSize, curParentBase]; nlinarith),
          hcore_res.2 ⟨i, hi⟩]
        dsimp only
        exact hfit_top.of_le (by have := (pTab[i]).isLt; omega))
    unfold finishArbProg
    refine ⟨⟨rfl, hfit_top, hcore.1.2.1, hcore.1.2.2, fun _ => hcpOut.1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hcore.2.1 ?_
      change (Memory.spec w).ValidHistory s₄
        ((Memory.spec w).clientHistory s₄
          (if (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 then
            Memory.write outAddr n >>= fun _ => copyWordsProg cpOut >>= fun _ => pure outAddr
          else Memory.write outAddr 0 >>= fun _ => pure outAddr))
      rw [hcore_res.1]
      simp only [↓reduceIte]
      exact validHistory_write_bind (by rw [hs₄_fr]; dsimp only [outAddr]; omega)
        (hfit_top.of_le (by omega))
        (validHistory_bind_step hcpOut.2.1 (validHistory_pure w _ _))
    · rw [memoryCost_bind']
      have hcore_r := hcore_res.1
      have cCore := hcore.2.2.1
      have cOut := hcpOut.2.2.1
      dsimp only [fa, ca, cpOut, s₄w, s₄, outAddr] at hcore_r cCore cOut ⊢
      rw [hcore_r]
      simp only [↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
      linarith only [cCore, cOut]
    · have hcore_r := hcore_res.1
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp [client_simps, hcore_r]
    · have hcore_r := hcore_res.1
      have hcore_m := hcore_res.2
      have hcpOut_m := hcpOut.2.2.2.2.1
      have hcpOut_v := hcpOut.2.2.2.2.2
      dsimp only [fa, ca, cpOut, s₄w, s₄, outAddr] at hcore_r hcore_m hcpOut_m hcpOut_v ⊢
      simp only [client_simps, hcore_r, ↓reduceIte]
      rw [hexp, outputList_eq_iff]
      refine ⟨?_, fun i => ?_⟩
      · simp only [List.length_map, List.length_finRange]
        rw [hcpOut_m (ws + wsSize n) (by omega)]
        exact Function.update_self _ _ _
      · have hi : i.1 < n := by simpa using i.isLt
        change ((Memory.spec 0).clientState _ _).mem (ws + wsSize n + 1 + i.1) =
          ((List.finRange n).map fun v => (pTab[v.1]).1)[i.1]
        simp only [List.getElem_map, List.getElem_finRange]
        rw [hcpOut_v i.1 hi, Function.update_of_ne (by dsimp only [wsSize, curParentBase]; omega)]
        exact (hcore_m ⟨i.1, hi⟩).trans (by simp)
    · rw [hexp]
      simp only [List.length_map, List.length_finRange]
      exact hfit_top.of_le (by omega)
  | none =>
    rw [haux] at hexp
    have hcore_res : (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 0 := by
      have h := hcore.2.2.2.2.2
      rwa [haux] at h
    unfold finishArbProg
    refine ⟨⟨rfl, hfit_top, hcore.1.2.1, hcore.1.2.2,
        fun h1' => by rw [hcore_res] at h1'; cases h1'⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hcore.2.1 ?_
      change (Memory.spec w).ValidHistory s₄
        ((Memory.spec w).clientHistory s₄
          (if (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 then _
          else Memory.write outAddr 0 >>= fun _ => pure outAddr))
      rw [hcore_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]
      exact validHistory_write_bind (by rw [hs₄_fr]; dsimp only [outAddr]; omega)
        (fits_zero w) (validHistory_pure w _ _)
    · rw [memoryCost_bind']
      have hcore_r := hcore_res
      have cCore := hcore.2.2.1
      dsimp only [fa, ca, outAddr] at hcore_r cCore ⊢
      rw [hcore_r]
      simp only [Nat.zero_ne_one, ↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
      linarith only [cCore]
    · have hcore_r := hcore_res
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp [client_simps, hcore_r]
    · have hcore_r := hcore_res
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp only [client_simps, hcore_r, Nat.zero_ne_one, ↓reduceIte]
      rw [hexp, outputList_eq_iff]
      exact ⟨Function.update_self _ _ _, fun i => Fin.elim0 i⟩
    · rw [hexp, List.length_nil]
      exact hfit_top.of_le (by omega)

private def edmondsProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := Prod.fst d
  let r := Prod.snd d
  let ws ← Memory.allocDirty (wsSize n)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← copyWordsProg ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  finishArbProg ⟨n, r, ws, outAddr⟩

private abbrev EdmondsProgSafe (w : ℕ) (d : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  let n := Prod.fst d
  let r := Prod.snd d
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let cp : CopyArgs := ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  let s3 := (Memory.spec 0).clientState s1 (copyWordsProg cp)
  Fits w (outAddr + (n + 1) + 8) ∧ r < n ∧
    iterationSafe copyStep CopyStepSafe w cp (2 * (n * n)) 0 s1 ∧
    FinishArbSafe w ⟨n, r, ws, outAddr⟩ s3

private theorem edmondsProg_realizes :
    Realizes .exact edmondsProg pairWords wordWords EdmondsProgSafe (fun _ _ => 0) := by
  unfold edmondsProg
  realize [copyWordsProg_realizes, finishArbProg_realizes]
  all_goals
    obtain ⟨hfit, hr, hcp, hfin⟩ := h
    first
    | exact hcp
    | exact hfin
    | exact hfit.of_le (by dsimp only [wsSize, curAdjBase]; nlinarith)

private theorem edmondsProg_spec {w M₀ : ℕ} (I : ArborescenceInput)
    (hM : ∀ u v, (I.cost u v).natAbs ≤ M₀) (hwb : Fits w (wordBound I.n M₀)) :
    let s₀ := Memory.State.init I.encode
    let d := (I.n, I.root.1)
    let outAddr := (Memory.spec 0).clientResult s₀ (edmondsProg d)
    let s' := (Memory.spec 0).clientState s₀ (edmondsProg d)
    EdmondsProgSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsProg d)) ∧
      memoryCost (edmondsProg d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + 8 * I.n + 3 ∧
      outputList s'.mem outAddr = I.expectedParentList ∧
      Fits w (outAddr + I.expectedParentList.length) := by
  rcases I with ⟨n, root, adj, cost⟩
  let I : ArborescenceInput := ⟨n, root, adj, cost⟩
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  have hws_eq : ws = 3 + 2 * (n * n) := by
    change I.encode.length + 1 = _
    simp [I, ArborescenceInput.encode]
    omega
  have hfit_top : Fits w (outAddr + (n + 1) + 8) :=
    hwb.of_le (by
      have hsq := sq_le_wordBound n M₀
      dsimp only [outAddr, ws, wsSize] at hws_eq ⊢
      rw [hws_eq]
      nlinarith only [hsq])
  obtain ⟨hfit_len1, hin_fits⟩ := inputFits_arb_encode I hM hwb
  have hwf0 := Memory.wellFormed_init hin_fits hfit_len1
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let cp : CopyArgs := ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  have hcp := copyWordsProg_spec cp s1
    (by dsimp only [cp, s1, outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; omega)
    (by dsimp only [cp, s1, outAddr, ws, wsSize, curAdjBase]; omega)
    (Or.inl (by dsimp only [cp, ws, curAdjBase] at hws_eq ⊢; rw [hws_eq]))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; omega))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize, curAdjBase]; omega))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize]; omega))
    (fun i _ => hwf0.mem_fits (3 + i))
  let s3 := (Memory.spec 0).clientState s1 (copyWordsProg cp)
  have hs3_fr : s3.frontier = outAddr + (n + 1) := hcp.2.2.2.1
  let a₀ := initAdjTable n fun u col => decide (I.digraph.Adj u col)
  let c₀ := initCostTable n cost
  have ha3 : ∀ u col : Fin n,
      s3.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0 := by
    intro u col
    have hlt : u.1 * n + col.1 < 2 * (n * n) := by
      have := List.mul_add_lt_sq u.isLt col.isLt; omega
    rw [show curAdjBase ws n + u.1 * n + col.1 = cp.dst + (u.1 * n + col.1) by
        dsimp only [cp, ws, curAdjBase]; omega,
      hcp.2.2.2.2.2 _ hlt]
    dsimp only [cp, s1, a₀, initAdjTable, ArborescenceInput.digraph, I]
    simp only [Vector.getElem_ofFn]
    exact init_mem_encode_arb_adj I u col
  have hc3 : ∀ u col : Fin n,
      s3.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1] := by
    intro u col
    have hlt : n * n + (u.1 * n + col.1) < 2 * (n * n) := by
      have := List.mul_add_lt_sq u.isLt col.isLt; omega
    rw [show curCostBase ws n + u.1 * n + col.1 = cp.dst + (n * n + (u.1 * n + col.1)) by
        dsimp only [cp, ws, curAdjBase, curCostBase]; omega,
      hcp.2.2.2.2.2 _ hlt]
    dsimp only [cp, s1, c₀, initCostTable]
    simp only [Vector.getElem_ofFn]
    simpa [Nat.add_assoc] using init_mem_encode_arb_cost I u col
  have hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀ := by
    intro u col; simp [c₀, initCostTable, hM u col]
  have hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => I.expectedParentList = (List.finRange n).map fun v => (pTab[v.1]).1
      | none => I.expectedParentList = [] := by
    have hmap_eq := edmonds_fin_map_eq I.digraph cost root
    unfold ArborescenceInput.expectedParentList
    dsimp only [I]
    cases haux : edmondsTableAux root n a₀ c₀ with
    | some pTab =>
      cases hedm : edmonds (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root with
      | none =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        simp at hmap_eq
      | some f =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        exact Option.some.inj hmap_eq
    | none =>
      cases hedm : edmonds (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root with
      | none => rfl
      | some f =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        simp at hmap_eq
  have hfin := finishArbProg_spec root a₀ c₀ s3 I.expectedParentList hfit_top hs3_fr hwb
    ha3 hc3 hB₀ hexp
  unfold edmondsProg
  dsimp only [I]
  refine ⟨⟨hfit_top, root.isLt, hcp.1, hfin.1⟩, ?_, ?_, ?_, ?_⟩
  · exact validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
        (validHistory_bind_step hcp.2.1 hfin.2.1))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [client_simps]
    have cCp := hcp.2.2.1
    have cFin := hfin.2.2.1
    dsimp only [s3, s1, cp, outAddr, ws, I] at cCp cFin ⊢
    have hid : 1 + (1 + (2 * (2 * (n * n)) + (43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1))) =
        43 * n ^ 3 + 22 * n ^ 2 + 8 * n + 3 := by ring
    linarith only [cCp, cFin, hid]
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.1
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.2

-- Transpose loader for `edmondsOutProg`

private structure TransposeRowArgs where
  n : ℕ
  u : ℕ
  ws : ℕ

private word_enc_structure encTransposeRowArgs : TransposeRowArgs where
  n : wordWords, u : wordWords, ws : wordWords

private instance : WordEncoding TransposeRowArgs := ⟨3, encTransposeRowArgs⟩

private def transposeRowStep (q : TransposeRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let col := Prod.snd q
  let a ← Memory.read (3 + col * env.n + env.u)
  let c ← Memory.read (3 + env.n * env.n + col * env.n + env.u)
  Memory.write (curAdjBase env.ws env.n + env.u * env.n + col) a
  Memory.write (curCostBase env.ws env.n + env.u * env.n + col) c
  pure (col + 1)

private abbrev TransposeRowStepSafe (w : ℕ) (q : TransposeRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  env.u < env.n ∧ col < env.n ∧ WsFits w env.ws env.n ∧ Fits w (3 + 2 * (env.n * env.n))

private theorem transposeRowStep_realizes :
    Realizes .exact transposeRowStep (appendWords encTransposeRowArgs wordWords) wordWords
      TransposeRowStepSafe (fun _ _ => 0) := by
  unfold transposeRowStep
  realize
  all_goals
    obtain ⟨hu, hc, hws, hin⟩ := h
    first
    | exact hin.of_le (by nlinarith)
    | exact hws.of_le (by dsimp only [wsSize, curAdjBase, curCostBase]; nlinarith)

private def fillTransposeRowProg (a : TransposeRowArgs) : Memory.Prog ℕ :=
  iterate transposeRowStep a a.n 0

private theorem fillTransposeRowProg_realizes :
    Realizes .exact fillTransposeRowProg encTransposeRowArgs wordWords
      (fun w a s => iterationSafe transposeRowStep TransposeRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillTransposeRowProg
  realize [transposeRowStep_realizes]
  exact h

private def transposeOuterStep (q : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillTransposeRowProg ⟨Prod.fst env, u, Prod.snd env⟩
  pure (u + 1)

private abbrev TransposeOuterStepSafe (w : ℕ) (q : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  Fits w (u + 1) ∧
    iterationSafe transposeRowStep TransposeRowStepSafe w ⟨Prod.fst env, u, Prod.snd env⟩
      (Prod.fst env) 0 s

private theorem transposeOuterStep_realizes :
    Realizes .exact transposeOuterStep (appendWords pairWords wordWords) wordWords
      TransposeOuterStepSafe (fun _ _ => 0) := by
  unfold transposeOuterStep
  realize [fillTransposeRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

private def transposeProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate transposeOuterStep d (Prod.fst d) 0

private theorem transposeProg_realizes :
    Realizes .exact transposeProg pairWords wordWords
      (fun w d s => iterationSafe transposeOuterStep TransposeOuterStepSafe w d (Prod.fst d) 0 s)
      (fun _ _ => 0) := by
  unfold transposeProg
  realize [transposeOuterStep_realizes]
  exact h

private theorem fillTransposeRowProg_spec {w n ws : ℕ} (uFin : Fin n)
    (adj : Fin n → Fin n → Bool) (cost : Fin n → Fin n → ℤ) (s : Memory.State)
    (hws : WsFits w ws n) (hin_fit : Fits w (3 + 2 * (n * n)))
    (hws_lo : 3 + 2 * (n * n) ≤ ws) (hf : ws + wsSize n ≤ s.frontier)
    (hadj_in : ∀ x y : Fin n, s.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0)
    (hcost_in : ∀ x y : Fin n, s.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y))
    (hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y))) :
    let ra : TransposeRowArgs := ⟨n, uFin.1, ws⟩
    let sr' := (Memory.spec 0).clientState s (fillTransposeRowProg ra)
    iterationSafe transposeRowStep TransposeRowStepSafe w ra n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillTransposeRowProg ra)) ∧
      memoryCost (fillTransposeRowProg ra) s ≤ 4 * n ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(curAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < curAdjBase ws n + uFin.1 * n + n ∨
        curCostBase ws n + uFin.1 * n ≤ addr ∧ addr < curCostBase ws n + uFin.1 * n + n) →
        sr'.mem addr = s.mem addr) ∧
      (∀ col : Fin n,
        sr'.mem (curAdjBase ws n + uFin.1 * n + col.1) = (if adj col uFin then 1 else 0) ∧
        sr'.mem (curCostBase ws n + uFin.1 * n + col.1) = Signed.encode (cost col uFin)) := by
  let ra : TransposeRowArgs := ⟨n, uFin.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := uFin.isLt
  have hrow := iterate_spec transposeRowStep TransposeRowStepSafe w ra 4 n
    (fun col idxR sr =>
      idxR = col ∧ sr.frontier = s.frontier ∧
        (∀ x y : Fin n, sr.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0) ∧
        (∀ x y : Fin n, sr.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y)) ∧
        (∀ c0 : Fin n, c0.1 < col →
          sr.mem (curAdjBase ws n + uFin.1 * n + c0.1) = (if adj c0 uFin then 1 else 0) ∧
          sr.mem (curCostBase ws n + uFin.1 * n + c0.1) = Signed.encode (cost c0 uFin)))
    (fun addr => curAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < curAdjBase ws n + uFin.1 * n + n ∨
      curCostBase ws n + uFin.1 * n ≤ addr ∧ addr < curCostBase ws n + uFin.1 * n + n)
    (fun col hcol idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hdone_r⟩ => by
      subst idxR
      set colFin : Fin n := ⟨col, hcol⟩
      have ha_cu : sr.mem (3 + col * n + uFin.1) = if adj colFin uFin then 1 else 0 := by
        simpa [Nat.add_assoc] using ha_r colFin uFin
      have hc_cu : sr.mem (3 + n * n + col * n + uFin.1) = Signed.encode (cost colFin uFin) := by
        simpa [Nat.add_assoc] using hc_r colFin uFin
      refine ⟨by dsimp only [TransposeRowStepSafe, ra]; exact ⟨hu_lt, hcol, hws, hin_fit⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold transposeRowStep
        dsimp only [ra]
        exact validHistory_read_bind
          (by dsimp only [wsSize] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize] at hf hfr_r ⊢; nlinarith)
            (validHistory_write_bind
              (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; nlinarith)
              (by rw [ha_cu]; split_ifs <;> first | exact h1 | exact fits_zero w)
              (validHistory_write_bind
                (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; nlinarith)
                (hc_cu ▸ hfit_c colFin uFin)
                (validHistory_pure w _ _))))
      · unfold transposeRowStep
        dsimp only [ra]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [transposeRowStep, ra, client_simps, hfr_r]
      · intro addr haddr
        simp only [transposeRowStep, ra, client_simps]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · unfold transposeRowStep
        dsimp only [ra]
        simp only [client_simps]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_⟩
        · intro x y
          have := x.isLt; have := y.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase]; nlinarith),
            Function.update_of_ne (by dsimp only [curAdjBase]; nlinarith)]
          exact ha_r x y
        · intro x y
          have := x.isLt; have := y.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase]; nlinarith),
            Function.update_of_ne (by dsimp only [curAdjBase]; nlinarith)]
          exact hc_r x y
        · intro c0 hc0
          by_cases heq : c0.1 = col
          · have hc0_eq : c0 = colFin := Fin.ext heq
            subst hc0_eq
            simp only [Function.update_self, colFin]
            rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith),
              Function.update_self]
            simp only [ha_cu, hc_cu]
            exact ⟨rfl, rfl⟩
          · rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith)]
            exact hdone_r c0 (by omega))
    0 s ⟨rfl, rfl, hadj_in, hcost_in, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, hdone_end⟩ := hrow
  unfold fillTransposeRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

private theorem transposeProg_spec {w n ws : ℕ} (hpos : 0 < n)
    (adj : Fin n → Fin n → Bool) (cost : Fin n → Fin n → ℤ) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hin_fit : Fits w (3 + 2 * (n * n)))
    (hws_lo : 3 + 2 * (n * n) ≤ ws) (hf : ws + wsSize n ≤ s₀.frontier)
    (hadj_in : ∀ x y : Fin n, s₀.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0)
    (hcost_in : ∀ x y : Fin n, s₀.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y))
    (hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y))) :
    let s' := (Memory.spec 0).clientState s₀ (transposeProg (n, ws))
    iterationSafe transposeOuterStep TransposeOuterStepSafe w (n, ws) n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (transposeProg (n, ws))) ∧
      memoryCost (transposeProg (n, ws)) s₀ ≤ (4 * n + 1) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if adj col u then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode (cost col u)) := by
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec transposeOuterStep TransposeOuterStepSafe w (n, ws) (4 * n + 1) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ x y : Fin n, s.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0) ∧
        (∀ x y : Fin n, s.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y)) ∧
        (∀ u col : Fin n, u.1 < m →
          s.mem (curAdjBase ws n + u.1 * n + col.1) = (if adj col u then 1 else 0) ∧
          s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode (cost col u)))
    (fun addr => curAdjBase ws n ≤ addr ∧ addr < curCostBase ws n + n * n)
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      have hrow := fillTransposeRowProg_spec uFin adj cost s hws hin_fit hws_lo
        (by rw [hfr]; exact hf) ha_s hc_s hfit_c
      have hdisj : ∀ addr, addr < curAdjBase ws n + m * n ∨
          curAdjBase ws n + m * n + n ≤ addr ∧ addr < curCostBase ws n + m * n ∨
          curCostBase ws n + m * n + n ≤ addr →
          ((Memory.spec 0).clientState s (fillTransposeRowProg ⟨n, m, ws⟩)).mem addr =
            s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, curAdjBase, curCostBase] at h ⊢; omega)
      refine ⟨by dsimp only [TransposeOuterStepSafe]; exact ⟨hws.of_le
          (by dsimp only [wsSize]; nlinarith), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold transposeOuterStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold transposeOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillTransposeRowProg ⟨n, m, ws⟩) s ≤ 4 * n := hrow.2.2.1
        simp only [client_simps]
        omega
      · unfold transposeOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold transposeOuterStep
        dsimp only
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hm)
              dsimp only [uFin, curAdjBase, curCostBase] at haddr ⊢
              rw [Nat.succ_mul] at this
              omega)
      · unfold transposeOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_⟩
        · intro x y
          have := List.mul_add_lt_sq x.isLt y.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact ha_s x y
        · intro x y
          have := List.mul_add_lt_sq x.isLt y.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact hc_s x y
        · intro u0 c0 hu0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu0) with hlt | heq
          · have hlt_mul : u0.1 * n + c0.1 < m * n := by
              have := c0.isLt
              have := Nat.mul_le_mul_right n hlt
              linarith [Nat.succ_mul u0.1 n]
            have hm_mul : m * n + n ≤ n * n := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hm
            rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega)),
              hdisj _ (Or.inr (Or.inl (by dsimp only [curAdjBase, curCostBase]; omega)))]
            exact hdone_o u0 c0 hlt
          · have hu_eq : u0 = uFin := Fin.ext heq
            subst hu_eq
            exact hrow.2.2.2.2.2 c0)
    0 s₀ ⟨rfl, rfl, hadj_in, hcost_in, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, _, _, _, _, _, hdone_end⟩ := h
  unfold transposeProg
  exact ⟨hsafe, hvh, hmc, hfr_end,
    fun u col => (hdone_end u col u.isLt).1,
    fun u col => (hdone_end u col u.isLt).2⟩

private def edmondsOutProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := Prod.fst d
  let r := Prod.snd d
  let ws ← Memory.allocDirty (wsSize n)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← transposeProg (n, ws)
  finishArbProg ⟨n, r, ws, outAddr⟩

private abbrev EdmondsOutProgSafe (w : ℕ) (d : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  let n := Prod.fst d
  let r := Prod.snd d
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let s3 := (Memory.spec 0).clientState s1 (transposeProg (n, ws))
  Fits w (outAddr + (n + 1) + 8) ∧ r < n ∧
    iterationSafe transposeOuterStep TransposeOuterStepSafe w (n, ws) n 0 s1 ∧
    FinishArbSafe w ⟨n, r, ws, outAddr⟩ s3

private theorem edmondsOutProg_realizes :
    Realizes .exact edmondsOutProg pairWords wordWords EdmondsOutProgSafe (fun _ _ => 0) := by
  unfold edmondsOutProg
  realize [transposeProg_realizes, finishArbProg_realizes]
  all_goals
    obtain ⟨hfit, hr, htr, hfin⟩ := h
    first
    | exact htr
    | exact hfin
    | exact hfit.of_le (by dsimp only [wsSize]; nlinarith)

private theorem edmondsOutProg_spec {w M₀ : ℕ} (I : ArborescenceInput)
    (hM : ∀ u v, (I.cost u v).natAbs ≤ M₀) (hwb : Fits w (wordBound I.n M₀)) :
    let s₀ := Memory.State.init I.encode
    let d := (I.n, I.root.1)
    let outAddr := (Memory.spec 0).clientResult s₀ (edmondsOutProg d)
    let s' := (Memory.spec 0).clientState s₀ (edmondsOutProg d)
    EdmondsOutProgSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsOutProg d)) ∧
      memoryCost (edmondsOutProg d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + 9 * I.n + 3 ∧
      outputList s'.mem outAddr = I.expectedOutParentList ∧
      Fits w (outAddr + I.expectedOutParentList.length) := by
  rcases I with ⟨n, root, adj, cost⟩
  let I : ArborescenceInput := ⟨n, root, adj, cost⟩
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  have hws_eq : ws = 3 + 2 * (n * n) := by
    change I.encode.length + 1 = _
    simp [I, ArborescenceInput.encode]
    omega
  have hfit_top : Fits w (outAddr + (n + 1) + 8) :=
    hwb.of_le (by
      have hsq := sq_le_wordBound n M₀
      dsimp only [outAddr, ws, wsSize] at hws_eq ⊢
      rw [hws_eq]
      nlinarith only [hsq])
  have hws_fit : WsFits w ws n := hfit_top.of_le (by dsimp only [outAddr, ws]; omega)
  obtain ⟨hfit_len1, hin_fits⟩ := inputFits_arb_encode I hM hwb
  have hwf0 := Memory.wellFormed_init hin_fits hfit_len1
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  have hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y)) := fun x y => by
    rw [← init_mem_encode_arb_cost I x y]
    exact hwf0.mem_fits _
  have htr := transposeProg_spec root.pos adj cost s1 hws_fit
    (hfit_top.of_le (by dsimp only [outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; nlinarith))
    (by rw [hws_eq])
    (by dsimp only [s1, outAddr, ws]; omega)
    (fun x y => init_mem_encode_arb_adj I x y)
    (fun x y => init_mem_encode_arb_cost I x y)
    hfit_c
  let s3 := (Memory.spec 0).clientState s1 (transposeProg (n, ws))
  have hs3_fr : s3.frontier = outAddr + (n + 1) := htr.2.2.2.1
  let a₀ := initAdjTable n fun u col => decide (I.digraph.Adj col u)
  let c₀ := initCostTable n fun u col => cost col u
  have ha3 : ∀ u col : Fin n,
      s3.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0 := by
    intro u col
    dsimp only [a₀, initAdjTable, ArborescenceInput.digraph, I]
    simp only [Vector.getElem_ofFn]
    exact htr.2.2.2.2.1 u col
  have hc3 : ∀ u col : Fin n,
      s3.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1] := by
    intro u col
    dsimp only [c₀, initCostTable]
    simp only [Vector.getElem_ofFn]
    exact htr.2.2.2.2.2 u col
  have hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀ := by
    intro u col; simp [c₀, initCostTable, hM col u]
  have hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => I.expectedOutParentList = (List.finRange n).map fun v => (pTab[v.1]).1
      | none => I.expectedOutParentList = [] := by
    have hmap_eq := edmondsOut_fin_map_eq I.digraph cost root
    unfold ArborescenceInput.expectedOutParentList
    dsimp only [I]
    cases haux : edmondsTableAux root n a₀ c₀ with
    | some pTab =>
      cases hedm : edmondsOut (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root with
      | none =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        simp at hmap_eq
      | some f =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        exact Option.some.inj hmap_eq
    | none =>
      cases hedm : edmondsOut (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root with
      | none => rfl
      | some f =>
        rw [hedm, show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl,
          haux] at hmap_eq
        simp at hmap_eq
  have hfin := finishArbProg_spec root a₀ c₀ s3 I.expectedOutParentList hfit_top hs3_fr hwb
    ha3 hc3 hB₀ hexp
  unfold edmondsOutProg
  dsimp only [I]
  refine ⟨⟨hfit_top, root.isLt, htr.1, hfin.1⟩, ?_, ?_, ?_, ?_⟩
  · exact validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
        (validHistory_bind_step htr.2.1 hfin.2.1))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [client_simps]
    have cTr := htr.2.2.1
    have cFin := hfin.2.2.1
    dsimp only [s3, s1, outAddr, ws, I] at cTr cFin ⊢
    have hid : 1 + (1 + ((4 * n + 1) * n + (43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1))) =
        43 * n ^ 3 + 22 * n ^ 2 + 9 * n + 3 := by ring
    linarith only [cTr, cFin, hid]
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.1
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.2


-- Super-root loader and branching extractor for `optimumBranchingProg`

private theorem init_mem_encode_branching_adj (I : BranchingInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (2 + (u.1 * I.n + v.1)) = if I.adj u v then 1 else 0 := by
  rw [show 2 + (u.1 * I.n + v.1) = ((u.1 * I.n + v.1) + 1) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((u.1 * I.n + v.1) + 1) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [BranchingInput.encode]
  rw [List.getD_cons_succ]
  have hlt : u.1 * I.n + v.1 < (flattenBoolMatrix I.n I.adj).length := by
    rw [length_flattenBoolMatrix]; exact List.mul_add_lt_sq u.isLt v.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  exact getD_flattenBoolMatrix I.n I.adj u v

private theorem init_mem_encode_branching_wt (I : BranchingInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (2 + I.n * I.n + (u.1 * I.n + v.1)) =
      Signed.encode (I.weight u v) := by
  rw [show 2 + I.n * I.n + (u.1 * I.n + v.1) =
    ((I.n * I.n + (u.1 * I.n + v.1)) + 1) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((I.n * I.n + (u.1 * I.n + v.1)) + 1) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [BranchingInput.encode]
  rw [List.getD_cons_succ]
  have hlen1 : (flattenBoolMatrix I.n I.adj).length = I.n * I.n :=
    length_flattenBoolMatrix I.n I.adj
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
  simp only [hlen1, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact getD_flattenSignedMatrix I.n I.weight u v

private theorem inputFits_branching_encode {w M₀ : ℕ} (I : BranchingInput)
    (hM : ∀ u v, (I.weight u v).natAbs ≤ M₀) (hwb : Fits w (wordBound (I.n + 1) M₀)) :
    Fits w (I.encode.length + 1) ∧ InputFits w I.encode := by
  have hsq := sq_le_wordBound (I.n + 1) M₀
  have hlen : I.encode.length = 1 + 2 * (I.n * I.n) := by
    simp [BranchingInput.encode, length_flattenBoolMatrix, length_flattenSignedMatrix]
    omega
  have hfit_len1 : Fits w (I.encode.length + 1) :=
    hwb.of_le (by rw [hlen]; nlinarith only [hsq])
  refine ⟨hfit_len1, hfit_len1.of_le (by omega), fun x hx => ?_⟩
  simp only [BranchingInput.encode, List.mem_cons] at hx
  rcases hx with rfl | hrest
  · exact hwb.of_le (by nlinarith only [hsq])
  · exact fits_mem_flatten_adj_signed I.adj I.weight hM hwb hrest

/-- Every word width fitting `I.wordBound` satisfies `InputFits w I.encode`. -/
public theorem BranchingInput.inputFits_encode {w : ℕ} (I : BranchingInput)
    (hwb : Fits w I.wordBound) : InputFits w I.encode :=
  (inputFits_branching_encode I I.natAbs_weight_le_maxAbsWeight hwb).2

private structure SuperRootRowArgs where
  n : ℕ
  x : ℕ
  ws : ℕ

private word_enc_structure encSuperRootRowArgs : SuperRootRowArgs where
  n : wordWords, x : wordWords, ws : wordWords

private instance : WordEncoding SuperRootRowArgs := ⟨3, encSuperRootRowArgs⟩

private def superRootRowStep (q : SuperRootRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let y := Prod.snd q
  let _ ← Memory.read 0
  let m := env.n + 1
  if env.x < env.n then
    if y < env.n then
      let a ← Memory.read (2 + y * env.n + env.x)
      let wtVal ← Memory.read (2 + env.n * env.n + y * env.n + env.x)
      let nw ← signedNegProg wtVal
      Memory.write (curAdjBase env.ws m + env.x * m + y) a
      Memory.write (curCostBase env.ws m + env.x * m + y) nw
      pure (y + 1)
    else
      Memory.write (curAdjBase env.ws m + env.x * m + y) 1
      Memory.write (curCostBase env.ws m + env.x * m + y) 0
      pure (y + 1)
  else
    Memory.write (curAdjBase env.ws m + env.x * m + y) 0
    Memory.write (curCostBase env.ws m + env.x * m + y) 0
    pure (y + 1)

private abbrev SuperRootRowStepSafe (w : ℕ) (q : SuperRootRowArgs × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let y := Prod.snd q
  let m := env.n + 1
  env.x < m ∧ y < m ∧ WsFits w env.ws m ∧ Fits w (2 + 2 * (env.n * env.n)) ∧
    (env.x < env.n → y < env.n →
      Fits w (s.mem (2 + env.n * env.n + y * env.n + env.x) + 1))

private theorem superRootRowStep_realizes :
    Realizes .exact superRootRowStep (appendWords encSuperRootRowArgs wordWords) wordWords
      SuperRootRowStepSafe (fun _ _ => 0) := by
  unfold superRootRowStep
  realize [signedNegProg_realizes]
  all_goals
    obtain ⟨hx_m, hy_m, hws, hin, hwt_fit⟩ := h
    first
    | exact hwt_fit ‹_› ‹_›
    | exact hin.of_le (by
        have : d.2 < d.1.n := ‹_›
        have : d.1.x < d.1.n := ‹_›
        nlinarith)
    | exact hws.of_le (by dsimp only [wsSize, curAdjBase, curCostBase]; nlinarith)

private def fillSuperRootRowProg (a : SuperRootRowArgs) : Memory.Prog ℕ :=
  iterate superRootRowStep a (a.n + 1) 0

private theorem fillSuperRootRowProg_realizes :
    Realizes .exact fillSuperRootRowProg encSuperRootRowArgs wordWords
      (fun w a s => iterationSafe superRootRowStep SuperRootRowStepSafe w a (a.n + 1) 0 s)
      (fun _ _ => 0) := by
  unfold fillSuperRootRowProg
  realize [superRootRowStep_realizes]
  all_goals first | exact h | exact h.1.2.2.1.of_le (by dsimp only [wsSize]; nlinarith)

private def superRootOuterStep (q : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let x := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillSuperRootRowProg ⟨Prod.fst env, x, Prod.snd env⟩
  pure (x + 1)

private abbrev SuperRootOuterStepSafe (w : ℕ) (q : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let x := Prod.snd q
  Fits w (x + 1) ∧
    iterationSafe superRootRowStep SuperRootRowStepSafe w ⟨Prod.fst env, x, Prod.snd env⟩
      (Prod.fst env + 1) 0 s

private theorem superRootOuterStep_realizes :
    Realizes .exact superRootOuterStep (appendWords pairWords wordWords) wordWords
      SuperRootOuterStepSafe (fun _ _ => 0) := by
  unfold superRootOuterStep
  realize [fillSuperRootRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

private def superRootProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate superRootOuterStep d (Prod.fst d + 1) 0

private theorem superRootProg_realizes :
    Realizes .exact superRootProg pairWords wordWords
      (fun w d s =>
        Fits w (Prod.fst d + 1) ∧
          iterationSafe superRootOuterStep SuperRootOuterStepSafe w d (Prod.fst d + 1) 0 s)
      (fun _ _ => 0) := by
  unfold superRootProg
  realize [superRootOuterStep_realizes]
  all_goals first | exact h.1 | exact h.2

private theorem fillSuperRootRowProg_spec {w n ws : ℕ} (xFin : Fin (n + 1))
    (G : Digraph (Fin n)) [DecidableRel G.Adj] (wt : Fin n → Fin n → ℤ) (s : Memory.State)
    (hws : WsFits w ws (n + 1)) (hin_fit : Fits w (2 + 2 * (n * n)))
    (hws_lo : 2 + 2 * (n * n) ≤ ws) (hf : ws + wsSize (n + 1) ≤ s.frontier)
    (hadj_in : ∀ u v : Fin n, s.mem (2 + (u.1 * n + v.1)) = if decide (G.Adj u v) then 1 else 0)
    (hwt_in : ∀ u v : Fin n, s.mem (2 + n * n + (u.1 * n + v.1)) = Signed.encode (wt u v))
    (hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (wt u v) + 1)) :
    let m := n + 1
    let ra : SuperRootRowArgs := ⟨n, xFin.1, ws⟩
    let sr' := (Memory.spec 0).clientState s (fillSuperRootRowProg ra)
    iterationSafe superRootRowStep SuperRootRowStepSafe w ra m 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillSuperRootRowProg ra)) ∧
      memoryCost (fillSuperRootRowProg ra) s ≤ 5 * m ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(curAdjBase ws m + xFin.1 * m ≤ addr ∧ addr < curAdjBase ws m + xFin.1 * m + m ∨
        curCostBase ws m + xFin.1 * m ≤ addr ∧ addr < curCostBase ws m + xFin.1 * m + m) →
        sr'.mem addr = s.mem addr) ∧
      (∀ y : Fin m,
        sr'.mem (curAdjBase ws m + xFin.1 * m + y.1) =
          (if (superRootAdjFin G)[xFin.1][y.1] then 1 else 0) ∧
        sr'.mem (curCostBase ws m + xFin.1 * m + y.1) =
          Signed.encode (superRootCostFin wt)[xFin.1][y.1]) := by
  let m := n + 1
  let ra : SuperRootRowArgs := ⟨n, xFin.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hx_lt := xFin.isLt
  have hrow := iterate_spec superRootRowStep SuperRootRowStepSafe w ra 5 m
    (fun y idxR sr =>
      idxR = y ∧ sr.frontier = s.frontier ∧
        (∀ u v : Fin n, sr.mem (2 + (u.1 * n + v.1)) = if decide (G.Adj u v) then 1 else 0) ∧
        (∀ u v : Fin n, sr.mem (2 + n * n + (u.1 * n + v.1)) = Signed.encode (wt u v)) ∧
        (∀ y0 : Fin m, y0.1 < y →
          sr.mem (curAdjBase ws m + xFin.1 * m + y0.1) =
            (if (superRootAdjFin G)[xFin.1][y0.1] then 1 else 0) ∧
          sr.mem (curCostBase ws m + xFin.1 * m + y0.1) =
            Signed.encode (superRootCostFin wt)[xFin.1][y0.1]))
    (fun addr => curAdjBase ws m + xFin.1 * m ≤ addr ∧ addr < curAdjBase ws m + xFin.1 * m + m ∨
      curCostBase ws m + xFin.1 * m ≤ addr ∧ addr < curCostBase ws m + xFin.1 * m + m)
    (fun y hy idxR sr ⟨hidxR, hfr_r, ha_r, hwt_r, hdone_r⟩ => by
      subst idxR
      set yFin : Fin m := ⟨y, hy⟩
      refine ⟨by
          dsimp only [SuperRootRowStepSafe, ra]
          refine ⟨hx_lt, hy, hws, hin_fit, fun hx_n hy_n => ?_⟩
          have hw_yx : sr.mem (2 + n * n + y * n + xFin.1) =
              Signed.encode (wt ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩) := by
            simpa [Nat.add_assoc] using hwt_r ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
          rw [hw_yx]
          exact hfit_wt1 ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold superRootRowStep
        dsimp only [ra]
        have hcell_xy := List.mul_add_lt_sq hx_lt hy
        refine validHistory_read_bind (by dsimp only [wsSize, m] at hf hfr_r ⊢; omega) ?_
        by_cases hx_n : xFin.1 < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n
          · simp only [hy_n, ↓reduceIte]
            have hcell_in := List.mul_add_lt_sq hy_n hx_n
            have ha_yx : sr.mem (2 + y * n + xFin.1) =
                if decide (G.Adj ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩) then 1 else 0 := by
              simpa [Nat.add_assoc] using ha_r ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
            have hw_yx : sr.mem (2 + n * n + y * n + xFin.1) =
                Signed.encode (wt ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩) := by
              simpa [Nat.add_assoc] using hwt_r ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
            refine validHistory_read_bind
              (by dsimp only [wsSize, m] at hf hfr_r hws_lo hcell_in ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, m] at hf hfr_r hws_lo hcell_in ⊢; omega) ?_)
            refine validHistory_bind_step (validHistory_signedNegProg w _ _) ?_
            rw [clientState_signedNegProg, hw_yx, clientResult_signedNegProg]
            refine validHistory_write_bind
              (by dsimp only [wsSize, curAdjBase, m] at hf hfr_r hcell_xy ⊢; omega)
              (by rw [ha_yx]; split_ifs <;> first | exact h1 | exact fits_zero w)
              (validHistory_write_bind
                (by dsimp only [wsSize, curCostBase, m] at hf hfr_r hcell_xy ⊢; omega)
                ?_ (validHistory_pure w _ _))
            have hfit1 := hfit_wt1 ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
            unfold Signed.encode at hfit1 ⊢
            rw [Int.natAbs_neg]
            exact hfit1.of_le (by split_ifs <;> omega)
          · simp only [hy_n, ↓reduceIte]
            exact validHistory_write_bind
              (by dsimp only [wsSize, curAdjBase, m] at hf hfr_r hcell_xy ⊢; omega) h1
              (validHistory_write_bind
                (by dsimp only [wsSize, curCostBase, m] at hf hfr_r hcell_xy ⊢; omega)
                (fits_zero w) (validHistory_pure w _ _))
        · simp only [hx_n, ↓reduceIte]
          exact validHistory_write_bind
            (by dsimp only [wsSize, curAdjBase, m] at hf hfr_r hcell_xy ⊢; omega) (fits_zero w)
            (validHistory_write_bind
              (by dsimp only [wsSize, curCostBase, m] at hf hfr_r hcell_xy ⊢; omega)
              (fits_zero w) (validHistory_pure w _ _))
      · unfold superRootRowStep
        dsimp only [ra]
        rw [memoryCost_bind', memoryCost_read, clientState_read]
        by_cases hx_n : xFin.1 < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n
          · simp only [hy_n, ↓reduceIte]
            rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
              memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
              memoryCost_bind', memoryCost_signedNegProg, clientState_signedNegProg,
              memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
            simp [client_simps]
          · simp only [hy_n, ↓reduceIte]
            rw [memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
            simp [client_simps]
        · simp only [hx_n, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
          simp [client_simps]
      · unfold superRootRowStep
        dsimp only [ra]
        by_cases hx_n : xFin.1 < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n <;> simp [hy_n, client_simps, hfr_r]
        · simp [hx_n, client_simps, hfr_r]
      · intro addr haddr
        have hneC : addr ≠ curCostBase ws m + xFin.1 * m + y := by omega
        have hneA : addr ≠ curAdjBase ws m + xFin.1 * m + y := by omega
        unfold superRootRowStep
        dsimp only [ra]
        by_cases hx_n : xFin.1 < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n
          · simp only [hy_n, ↓reduceIte, client_simps]
            rw [Function.update_of_ne hneC, Function.update_of_ne hneA]
          · simp only [hy_n, ↓reduceIte, client_simps]
            rw [Function.update_of_ne hneC, Function.update_of_ne hneA]
        · simp only [hx_n, ↓reduceIte, client_simps]
          rw [Function.update_of_ne hneC, Function.update_of_ne hneA]
      · unfold superRootRowStep
        dsimp only [ra]
        have hcell_xy := List.mul_add_lt_sq hx_lt hy
        by_cases hx_n : xFin.1 < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n
          · have ha_yx : sr.mem (2 + y * n + xFin.1) =
                if decide (G.Adj ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩) then 1 else 0 := by
              simpa [Nat.add_assoc] using ha_r ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
            have hw_yx : sr.mem (2 + n * n + y * n + xFin.1) =
                Signed.encode (wt ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩) := by
              simpa [Nat.add_assoc] using hwt_r ⟨y, hy_n⟩ ⟨xFin.1, hx_n⟩
            simp only [hy_n, ↓reduceIte, client_simps, hw_yx, clientResult_signedNegProg]
            refine ⟨trivial, hfr_r, ?_, ?_, ?_⟩
            · intro u v
              have := List.mul_add_lt_sq u.isLt v.isLt
              rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
              exact ha_r u v
            · intro u v
              have := List.mul_add_lt_sq u.isLt v.isLt
              rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
              exact hwt_r u v
            · intro y0 hy0
              by_cases heq : y0.1 = y
              · have hy0_eq : y0 = yFin := Fin.ext heq
                subst hy0_eq
                simp only [m, yFin, Function.update_self]
                rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; omega),
                  Function.update_self]
                simp [ha_yx, superRootAdjFin, superRootCostFin, initAdjTable, initCostTable,
                  hx_n, hy_n]
              · rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega)]
                exact hdone_r y0 (by omega)
          · simp only [hy_n, ↓reduceIte, client_simps]
            refine ⟨trivial, hfr_r, ?_, ?_, ?_⟩
            · intro u v
              have := List.mul_add_lt_sq u.isLt v.isLt
              rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
              exact ha_r u v
            · intro u v
              have := List.mul_add_lt_sq u.isLt v.isLt
              rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
              exact hwt_r u v
            · intro y0 hy0
              by_cases heq : y0.1 = y
              · have hy0_eq : y0 = yFin := Fin.ext heq
                subst hy0_eq
                simp only [m, yFin, Function.update_self]
                rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; omega),
                  Function.update_self]
                simp [superRootAdjFin, superRootCostFin, initAdjTable, initCostTable,
                  hx_n, hy_n, Signed.encode]
              · rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                  Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega)]
                exact hdone_r y0 (by omega)
        · simp only [hx_n, ↓reduceIte, client_simps]
          refine ⟨trivial, hfr_r, ?_, ?_, ?_⟩
          · intro u v
            have := List.mul_add_lt_sq u.isLt v.isLt
            rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
              Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
            exact ha_r u v
          · intro u v
            have := List.mul_add_lt_sq u.isLt v.isLt
            rw [Function.update_of_ne (by dsimp only [curCostBase, m]; omega),
              Function.update_of_ne (by dsimp only [curAdjBase, m]; omega)]
            exact hwt_r u v
          · intro y0 hy0
            by_cases heq : y0.1 = y
            · have hy0_eq : y0 = yFin := Fin.ext heq
              subst hy0_eq
              simp only [m, yFin, Function.update_self]
              rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; omega),
                Function.update_self]
              simp [superRootAdjFin, superRootCostFin, initAdjTable, initCostTable,
                hx_n, Signed.encode]
            · rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
                Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega)]
              exact hdone_r y0 (by omega))
    0 s ⟨rfl, rfl, hadj_in, hwt_in, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, hdone_end⟩ := hrow
  unfold fillSuperRootRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun y => hdone_end y y.isLt⟩

private theorem superRootProg_spec {w n ws : ℕ}
    (G : Digraph (Fin n)) [DecidableRel G.Adj] (wt : Fin n → Fin n → ℤ) (s₀ : Memory.State)
    (hws : WsFits w ws (n + 1)) (hin_fit : Fits w (2 + 2 * (n * n)))
    (hws_lo : 2 + 2 * (n * n) ≤ ws) (hf : ws + wsSize (n + 1) ≤ s₀.frontier)
    (hadj_in : ∀ u v : Fin n, s₀.mem (2 + (u.1 * n + v.1)) = if decide (G.Adj u v) then 1 else 0)
    (hwt_in : ∀ u v : Fin n, s₀.mem (2 + n * n + (u.1 * n + v.1)) = Signed.encode (wt u v))
    (hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (wt u v) + 1)) :
    let m := n + 1
    let s' := (Memory.spec 0).clientState s₀ (superRootProg (n, ws))
    (Fits w m ∧ iterationSafe superRootOuterStep SuperRootOuterStepSafe w (n, ws) m 0 s₀) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (superRootProg (n, ws))) ∧
      memoryCost (superRootProg (n, ws)) s₀ ≤ (5 * m + 1) * m ∧
      s'.frontier = s₀.frontier ∧
      (∀ x y : Fin m,
        s'.mem (curAdjBase ws m + x.1 * m + y.1) =
          if (superRootAdjFin G)[x.1][y.1] then 1 else 0) ∧
      (∀ x y : Fin m,
        s'.mem (curCostBase ws m + x.1 * m + y.1) =
          Signed.encode (superRootCostFin wt)[x.1][y.1]) := by
  let m := n + 1
  have hfit_m : Fits w m := hws.of_le (by dsimp only [wsSize, m]; nlinarith)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec superRootOuterStep SuperRootOuterStepSafe w (n, ws) (5 * m + 1) m
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ u v : Fin n, s.mem (2 + (u.1 * n + v.1)) = if decide (G.Adj u v) then 1 else 0) ∧
        (∀ u v : Fin n, s.mem (2 + n * n + (u.1 * n + v.1)) = Signed.encode (wt u v)) ∧
        (∀ x y : Fin m, x.1 < k →
          s.mem (curAdjBase ws m + x.1 * m + y.1) =
            (if (superRootAdjFin G)[x.1][y.1] then 1 else 0) ∧
          s.mem (curCostBase ws m + x.1 * m + y.1) =
            Signed.encode (superRootCostFin wt)[x.1][y.1]))
    (fun addr => curAdjBase ws m ≤ addr ∧ addr < curCostBase ws m + m * m)
    (fun k hk idx s ⟨hidx, hfr, ha_s, hwt_s, hdone_o⟩ => by
      subst idx
      let xFin : Fin m := ⟨k, hk⟩
      have hrow := fillSuperRootRowProg_spec xFin G wt s hws hin_fit hws_lo
        (by rw [hfr]; exact hf) ha_s hwt_s hfit_wt1
      have hdisj : ∀ addr, addr < curAdjBase ws m + k * m ∨
          curAdjBase ws m + k * m + m ≤ addr ∧ addr < curCostBase ws m + k * m ∨
          curCostBase ws m + k * m + m ≤ addr →
          ((Memory.spec 0).clientState s (fillSuperRootRowProg ⟨n, k, ws⟩)).mem addr =
            s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [xFin, curAdjBase, curCostBase, m] at h ⊢; omega)
      refine ⟨by dsimp only [SuperRootOuterStepSafe]; exact ⟨hws.of_le
          (by dsimp only [wsSize, m] at hk ⊢; nlinarith), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold superRootOuterStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold superRootOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillSuperRootRowProg ⟨n, k, ws⟩) s ≤ 5 * m := hrow.2.2.1
        simp only [client_simps]
        omega
      · unfold superRootOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [xFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold superRootOuterStep
        dsimp only
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by have hmul_le := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hk)
              rw [Nat.succ_mul] at hmul_le
              dsimp only [xFin, curAdjBase, curCostBase, m] at hmul_le haddr ⊢
              omega)
      · unfold superRootOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [xFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_⟩
        · intro u v
          have := List.mul_add_lt_sq u.isLt v.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact ha_s u v
        · intro u v
          have := List.mul_add_lt_sq u.isLt v.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact hwt_s u v
        · intro x0 y0 hx0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx0) with hlt | heq
          · have hlt_mul : x0.1 * m + y0.1 < k * m := by
              have := y0.isLt
              have := Nat.mul_le_mul_right m hlt
              linarith [Nat.succ_mul x0.1 m]
            have hk_mul : k * m + m ≤ m * m := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right m hk
            rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega)),
              hdisj _ (Or.inr (Or.inl (by dsimp only [curAdjBase, curCostBase]; omega)))]
            exact hdone_o x0 y0 hlt
          · have hx_eq : x0 = xFin := Fin.ext heq
            subst hx_eq
            exact hrow.2.2.2.2.2 y0)
    0 s₀ ⟨rfl, rfl, hadj_in, hwt_in, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, _, _, _, _, _, hdone_end⟩ := h
  unfold superRootProg
  exact ⟨⟨hfit_m, hsafe⟩, hvh, hmc, hfr_end,
    fun x y => (hdone_end x y x.isLt).1,
    fun x y => (hdone_end x y x.isLt).2⟩

private structure ExtractArgs where
  n : ℕ
  src : ℕ
  dst : ℕ

private word_enc_structure encExtractArgs : ExtractArgs where
  n : wordWords, src : wordWords, dst : wordWords

private instance : WordEncoding ExtractArgs := ⟨3, encExtractArgs⟩

private def extractBranchingStep (q : ExtractArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let v := Prod.snd q
  let pv ← Memory.read (env.src + v)
  let outVal := if pv < env.n then pv else v
  Memory.write (env.dst + v) outVal
  pure (v + 1)

private abbrev ExtractStepSafe (w : ℕ) (q : ExtractArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let v := Prod.snd q
  Fits w (env.src + v) ∧ Fits w (env.dst + v) ∧ Fits w (v + 1)

private theorem extractBranchingStep_realizes :
    Realizes .exact extractBranchingStep (appendWords encExtractArgs wordWords) wordWords
      ExtractStepSafe (fun _ _ => 0) := by
  unfold extractBranchingStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def extractBranchingProg (a : ExtractArgs) : Memory.Prog ℕ :=
  iterate extractBranchingStep a a.n 0

private theorem extractBranchingProg_realizes :
    Realizes .exact extractBranchingProg encExtractArgs wordWords
      (fun w a s => iterationSafe extractBranchingStep ExtractStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold extractBranchingProg
  realize [extractBranchingStep_realizes]
  exact h

private theorem extractBranchingProg_spec {w : ℕ} (a : ExtractArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.n ≤ s₀.frontier) (hdst_f : a.dst + a.n ≤ s₀.frontier)
    (hdisj : a.src + a.n ≤ a.dst)
    (hfit_src : Fits w (a.src + a.n)) (hfit_dst : Fits w (a.dst + a.n))
    (hfit_n : Fits w a.n) :
    let s' := (Memory.spec 0).clientState s₀ (extractBranchingProg a)
    iterationSafe extractBranchingStep ExtractStepSafe w a a.n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (extractBranchingProg a)) ∧
      memoryCost (extractBranchingProg a) s₀ ≤ 2 * a.n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.dst ≤ addr ∧ addr < a.dst + a.n) → s'.mem addr = s₀.mem addr) ∧
      (∀ i < a.n, s'.mem (a.dst + i) =
        if s₀.mem (a.src + i) < a.n then s₀.mem (a.src + i) else i) := by
  have h := iterate_spec extractBranchingStep ExtractStepSafe w a 2 a.n
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ j < a.n, s.mem (a.src + j) = s₀.mem (a.src + j)) ∧
        (∀ j < k, s.mem (a.dst + j) =
          if s₀.mem (a.src + j) < a.n then s₀.mem (a.src + j) else j))
    (fun addr => a.dst ≤ addr ∧ addr < a.dst + a.n)
    (fun k hk idx s ⟨hidx, hfr, hsrc_eq, hdone⟩ => by
      subst idx
      have hk_val := hsrc_eq k hk
      refine ⟨by dsimp only [ExtractStepSafe]; exact ⟨hfit_src.of_le (by omega),
          hfit_dst.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold extractBranchingStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_write_bind (by omega)
            (by split_ifs <;> exact hfit_n.of_le (by omega))
            (validHistory_pure w _ _))
      · unfold extractBranchingStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [extractBranchingStep, client_simps, hfr]
      · intro addr haddr
        simp only [extractBranchingStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold extractBranchingStep
        dsimp only
        simp only [client_simps, hk_val]
        refine ⟨trivial, hfr, ?_, ?_⟩
        · intro j hj
          rw [Function.update_of_ne (by omega)]
          exact hsrc_eq j hj
        · intro j hj
          by_cases heq : j = k
          · subst heq; simp
          · rw [Function.update_of_ne (by omega)]
            exact hdone j (by omega))
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hdone_e⟩ := h
  unfold extractBranchingProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, hdone_e⟩

private def optimumBranchingProg (n : ℕ) : Memory.Prog ℕ := do
  let m := n + 1
  let ws ← Memory.allocDirty (wsSize m)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← superRootProg (n, ws)
  let _ ← edmondsCoreProg ⟨m, n, ws⟩
  Memory.write outAddr n
  let _ ← extractBranchingProg ⟨n, curParentBase ws m, outAddr + 1⟩
  pure outAddr

private abbrev OptimumBranchingProgSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  let m := n + 1
  let ws := s₀.frontier
  let outAddr := ws + wsSize m
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let s3 := (Memory.spec 0).clientState s1 (superRootProg (n, ws))
  let ca : CoreArgs := ⟨m, n, ws⟩
  let res := (Memory.spec 0).clientResult s3 (forwardProg ca)
  let sf := (Memory.spec 0).clientState s3 (forwardProg ca)
  let s4 := (Memory.spec 0).clientState s3 (edmondsCoreProg ca)
  let s4w : Memory.State := ⟨Function.update s4.mem outAddr n, s4.frontier⟩
  Fits w (outAddr + (n + 1) + 8) ∧
    iterationSafe superRootOuterStep SuperRootOuterStepSafe w (n, ws) m 0 s1 ∧
    iterationSafe forwardStep ForwardStepSafe w ca m ⟨0, 0, 0⟩ s3 ∧
    (res.status = 1 →
      iterationSafe backwardStep BackwardStepSafe w ⟨m, ws, res.depth⟩ res.depth 0 sf) ∧
    iterationSafe extractBranchingStep ExtractStepSafe w
      ⟨n, curParentBase ws m, outAddr + 1⟩ n 0 s4w

private theorem optimumBranchingProg_realizes :
    Realizes .exact optimumBranchingProg wordWords wordWords
      OptimumBranchingProgSafe (fun _ _ => 0) := by
  unfold optimumBranchingProg
  realize [superRootProg_realizes, edmondsCoreProg_realizes, extractBranchingProg_realizes]
  all_goals
    obtain ⟨hfit, hsr, hfwd, hbwd, hext⟩ := h
    first
    | exact hsr
    | exact hfwd
    | exact hbwd
    | exact hext
    | exact hfit.of_le (by dsimp only [wsSize, curParentBase, frameBase]; nlinarith)

private theorem optimumBranchingProg_spec {w M₀ : ℕ} (I : BranchingInput)
    (hM : ∀ u v, (I.weight u v).natAbs ≤ M₀) (hwb : Fits w (wordBound (I.n + 1) M₀)) :
    let s₀ := Memory.State.init I.encode
    let n := I.n
    let outAddr := (Memory.spec 0).clientResult s₀ (optimumBranchingProg n)
    let s' := (Memory.spec 0).clientState s₀ (optimumBranchingProg n)
    OptimumBranchingProgSafe w n s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (optimumBranchingProg n)) ∧
      memoryCost (optimumBranchingProg n) s₀ ≤
        43 * (I.n + 1) ^ 3 + 23 * (I.n + 1) ^ 2 + 9 * (I.n + 1) + 3 ∧
      outputList s'.mem outAddr = I.expectedParentList ∧
      Fits w (outAddr + I.expectedParentList.length) := by
  rcases I with ⟨n, adj, weight⟩
  let I : BranchingInput := ⟨n, adj, weight⟩
  let m := n + 1
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let outAddr := ws + wsSize m
  have hws_eq : ws = 2 + 2 * (n * n) := by
    change I.encode.length + 1 = _
    simp [I, BranchingInput.encode, length_flattenBoolMatrix, length_flattenSignedMatrix]
    omega
  have hfit_top : Fits w (outAddr + (n + 1) + 8) :=
    hwb.of_le (by
      have hsq := sq_le_wordBound (n + 1) M₀
      dsimp only [outAddr, ws, m, wsSize] at hws_eq ⊢
      rw [hws_eq]
      nlinarith only [hsq])
  have hws_fit : WsFits w ws m := hfit_top.of_le (by dsimp only [outAddr, ws]; omega)
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  have hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (weight u v) + 1) :=
    fun u v => fits_signedEncode_add_one_of_wordBound (hM u v) hwb
  let G : Digraph (Fin n) := BranchingInput.digraph ⟨n, adj, weight⟩
  have hsr := superRootProg_spec G weight s1 hws_fit
    (hfit_top.of_le (by dsimp only [outAddr, ws, m, wsSize] at hws_eq ⊢; rw [hws_eq]; nlinarith))
    (by rw [hws_eq])
    (by dsimp only [s1, outAddr, ws, m]; omega)
    (fun u v => by
      change (Memory.State.init I.encode).mem (2 + (u.1 * I.n + v.1)) = _
      rw [init_mem_encode_branching_adj I u v]
      simp [I, G, BranchingInput.digraph])
    (fun u v => init_mem_encode_branching_wt I u v)
    hfit_wt1
  let s3 := (Memory.spec 0).clientState s1 (superRootProg (n, ws))
  have hs3_fr : s3.frontier = outAddr + (n + 1) := hsr.2.2.2.1
  let a₀ := superRootAdjFin G
  let c₀ := superRootCostFin weight
  have hB₀ : ∀ x y : Fin m, (c₀[x.1][y.1]).natAbs ≤ M₀ := by
    intro x y
    simp only [c₀, superRootCostFin, initCostTable, Vector.getElem_ofFn]
    split_ifs with hx hy
    · rw [Int.natAbs_neg]
      exact hM ⟨y.1, hy⟩ ⟨x.1, hx⟩
    · simp
    · simp
  have hcore := edmondsCoreProg_spec (Fin.last n) a₀ c₀ s3 hws_fit
    (by rw [hs3_fr]; dsimp only [outAddr, ws, m]; omega) hwb
    hsr.2.2.2.2.1 hsr.2.2.2.2.2 hB₀
  let ca : CoreArgs := ⟨m, n, ws⟩
  let s4 := (Memory.spec 0).clientState s3 (edmondsCoreProg ca)
  have hs4_fr : s4.frontier = outAddr + (n + 1) := hcore.2.2.2.1.trans hs3_fr
  obtain ⟨pTab, haux, hp_val⟩ := optimumBranchingParent_fin_eq G weight
  have hcore_res : (Memory.spec 0).clientResult s3 (edmondsCoreProg ca) = 1 ∧
       ∀ v : Fin m, s4.mem (curParentBase ws m + v.1) = (pTab[v.1]).1 := by
    have h := hcore.2.2.2.2.2
    rwa [show edmondsTableAux (Fin.last n) m a₀ c₀ = some pTab from haux] at h
  let s4w : Memory.State := ⟨Function.update s4.mem outAddr n, s4.frontier⟩
  let extA : ExtractArgs := ⟨n, curParentBase ws m, outAddr + 1⟩
  have hext := extractBranchingProg_spec extA s4w
    (by dsimp only [extA, s4w]; rw [hs4_fr]; dsimp only [outAddr, ws, m, wsSize, curParentBase];
        nlinarith)
    (by dsimp only [extA, s4w]; rw [hs4_fr]; dsimp only [outAddr, ws]; omega)
    (by dsimp only [extA, outAddr, ws, m, wsSize, curParentBase]; nlinarith)
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws, m, wsSize, curParentBase]; nlinarith))
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws]; omega))
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws]; omega))
  have hsafe : OptimumBranchingProgSafe w n s₀ :=
    ⟨hfit_top, hsr.1.2, hcore.1.2.1, hcore.1.2.2, hext.1⟩
  unfold optimumBranchingProg
  dsimp only [I]
  refine ⟨hsafe, ?_, ?_, ?_, ?_⟩
  · refine validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega)) ?_)
    refine validHistory_bind_step hsr.2.1 (validHistory_bind_step hcore.2.1 ?_)
    exact validHistory_write_bind (by rw [hs4_fr]; dsimp only [outAddr, ws, m]; omega)
      (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega))
      (validHistory_bind_step hext.2.1 (validHistory_pure w _ _))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [memoryCost_write, client_simps]
    have cSr := hsr.2.2.1
    have cCore := hcore.2.2.1
    have cExt := hext.2.2.1
    dsimp only [s4w, s4, s3, s1, ca, extA, outAddr, ws, m, I] at cSr cCore cExt ⊢
    have hid : 1 + (1 + ((5 * (n + 1) + 1) * (n + 1) +
        ((43 * (n + 1) ^ 3 + 18 * (n + 1) ^ 2 + 6 * (n + 1)) + (1 + (2 * n + 0))))) + 2 =
        43 * (n + 1) ^ 3 + 23 * (n + 1) ^ 2 + 9 * (n + 1) + 3 := by ring
    linarith only [cSr, cCore, cExt, hid]
  · have hext_m := hext.2.2.2.2.1
    have hext_v := hext.2.2.2.2.2
    have hcore_m := hcore_res.2
    unfold BranchingInput.expectedParentList
    dsimp only [s4w, s4, s3, s1, ca, extA, outAddr, ws, m, I, G] at hext_m hext_v hcore_m hp_val ⊢
    simp only [client_simps]
    rw [outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · simp only [List.length_map, List.length_finRange]
      rw [hext_m (s₀.frontier + wsSize (n + 1)) (by omega)]
      exact Function.update_self _ _ _
    · have hi : i.1 < n := by simpa using i.isLt
      change ((Memory.spec 0).clientState _ _).mem (s₀.frontier + wsSize (n + 1) + 1 + i.1) =
        ((List.finRange n).map fun v =>
          (optimumBranchingParent (BranchingInput.digraph ⟨n, adj, weight⟩) weight v).1)[i.1]
      simp only [List.getElem_map, List.getElem_finRange]
      rw [hext_v i.1 hi, hp_val]
      have hval_i :
          (Function.update
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                { mem := s₀.mem, frontier := s₀.frontier + wsSize (n + 1) + (n + 1) }
                (superRootProg (n, s₀.frontier)))
              (edmondsCoreProg { n := n + 1, r := n, ws := s₀.frontier })).mem
            (s₀.frontier + wsSize (n + 1)) n)
            (curParentBase s₀.frontier (n + 1) + i.1) =
          (pTab[i.1]).1 := by
        rw [Function.update_of_ne (by dsimp only [wsSize, curParentBase]; omega)]
        exact hcore_m ⟨i.1, by omega⟩
      simp [hval_i]
  · simp only [client_simps, BranchingInput.expectedParentList, List.length_map,
      List.length_finRange]
    exact hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega)

private theorem executesList_of_client_spec {α : Type} {k r C₁ w K n : ℕ}
    {enc : α ↪ (Fin k → ℕ)} {f : α → Memory.Prog ℕ} {Safe : ℕ → α → Memory.State → Prop}
    {pc : ℕ} {prog : Program .standard r} {frontier : Fin r} {out : Fin 1 → Fin r}
    (he : ∀ (w : ℕ) (a : α) (xs : List ℕ),
      (∀ j : Fin k, xs.getD j.val 0 = enc a j) →
      k ≤ xs.length → Fits w (xs.length + 1) → InputFits w xs →
      Safe w a (Memory.State.init xs) →
      (Memory.spec w).ValidHistory (Memory.State.init xs)
        ((Memory.spec w).clientHistory (Memory.State.init xs) (f a)) →
      ∃ y m, Runs w prog (State.init xs) ⟨pc, y⟩ m ∧
        step w prog ⟨pc, y⟩ =
          .halt (wordWords ((Memory.spec w).clientResult (Memory.State.init xs) (f a)) 0) ∧
        memoryState frontier y =
          (Memory.spec w).clientState (Memory.State.init xs) (f a) ∧
        (∀ j, y.regs (out j) =
          wordWords ((Memory.spec w).clientResult (Memory.State.init xs) (f a)) j) ∧
        m + 1 ≤ C₁ * (memoryCost (f a) (Memory.State.init xs) + 0 + 1) + 1)
    (a : α) (xs expected : List ℕ)
    (hlayout : ∀ j : Fin k, xs.getD j.val 0 = enc a j)
    (hk : k ≤ xs.length) (hfit_len : Fits w (xs.length + 1)) (hin_fits : InputFits w xs)
    (hsafe : Safe w a (Memory.State.init xs))
    (hvh : (Memory.spec w).ValidHistory (Memory.State.init xs)
      ((Memory.spec w).clientHistory (Memory.State.init xs) (f a)))
    (hmc : memoryCost (f a) (Memory.State.init xs) + 1 ≤ K * (n + 1) ^ 3)
    (hout : outputList ((Memory.spec 0).clientState (Memory.State.init xs) (f a)).mem
      ((Memory.spec 0).clientResult (Memory.State.init xs) (f a)) = expected)
    (hfit_out :
      Fits w ((Memory.spec 0).clientResult (Memory.State.init xs) (f a) + expected.length)) :
    ∃ t, ExecutesList w prog (State.init xs) expected t ∧
      t ≤ (K * C₁ + 1) * (n + 1) ^ 3 := by
  obtain ⟨y, m, hruns, hhalt, hmem, _, hsteps⟩ :=
    he w a xs hlayout hk hfit_len hin_fits hsafe hvh
  rw [clientState_width w] at hmem
  rw [clientResult_width w] at hhalt
  dsimp only [wordWords] at hhalt
  have hymem :
      y.mem = ((Memory.spec 0).clientState (Memory.State.init xs) (f a)).mem :=
    congrArg Memory.State.mem hmem
  refine ⟨m + 1, ⟨⟨pc, y⟩, m, _, hruns, hhalt, hymem ▸ hout, hfit_out, rfl⟩, ?_⟩
  have hmul : C₁ * (memoryCost (f a) (Memory.State.init xs) + 0 + 1) ≤ C₁ * (K * (n + 1) ^ 3) :=
    Nat.mul_le_mul_left C₁ (by omega)
  have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow 3 (n + 1) (Nat.succ_pos _)
  have hring : C₁ * (K * (n + 1) ^ 3) + (n + 1) ^ 3 = (K * C₁ + 1) * (n + 1) ^ 3 := by ring
  linarith only [hsteps, hmul, hpos, hring]

private theorem exists_arb_program_of_spec
    {f : ℕ × ℕ → Memory.Prog ℕ} {Safe : ℕ → ℕ × ℕ → Memory.State → Prop}
    {expected : ArborescenceInput → List ℕ} {lin : ℕ} (hlin : lin ≤ 129)
    (hreal : Realizes .exact f pairWords wordWords Safe (fun _ _ => 0))
    (hspec : ∀ {w M₀ : ℕ} (I : ArborescenceInput),
      (∀ u v, (I.cost u v).natAbs ≤ M₀) → Fits w (wordBound I.n M₀) →
      let s₀ := Memory.State.init I.encode
      let d := (I.n, I.root.1)
      let outAddr := (Memory.spec 0).clientResult s₀ (f d)
      let s' := (Memory.spec 0).clientState s₀ (f d)
      Safe w d s₀ ∧
        (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (f d)) ∧
        memoryCost (f d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + lin * I.n + 3 ∧
        outputList s'.mem outAddr = expected I ∧
        Fits w (outAddr + (expected I).length)) :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) expected := by
  obtain ⟨r, C₁, pc, prog, hnw, frontier, _, he⟩ :=
    hreal.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, 43 * C₁ + 1, prog, hnw, fun I w hwb _ => ?_⟩
  obtain ⟨hfit_len, hin_fits⟩ := inputFits_arb_encode I I.natAbs_cost_le_maxAbsCost hwb
  have hs := hspec I I.natAbs_cost_le_maxAbsCost hwb
  exact executesList_of_client_spec he (I.n, I.root.1) I.encode (expected I)
    (by rintro ⟨_ | _ | _, h⟩; exacts [rfl, rfl, by omega])
    (by simp [ArborescenceInput.encode]) hfit_len hin_fits hs.1 hs.2.1
    (by
      have hmc := hs.2.2.1
      have hsq0 := Nat.zero_le (I.n ^ 2)
      have hlin_mul : lin * I.n ≤ 129 * I.n := Nat.mul_le_mul_right I.n hlin
      have hexp : 43 * (I.n + 1) ^ 3 = 43 * I.n ^ 3 + 129 * I.n ^ 2 + 129 * I.n + 43 := by ring
      linarith only [hmc, hexp, hsq0, hlin_mul])
    hs.2.2.2.1 hs.2.2.2.2

/-! ### Main `O(n³)` Word-RAM running-time theorems -/

public section

/-- Materialized-table Chu–Liu/Edmonds minimum-cost spanning in-arborescence runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 1) * I.maxAbsCost + 32 * (I.n + 1) ^ 2` bounds word values and addresses,
so `w` of order `log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
theorem exists_edmonds_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) ArborescenceInput.expectedParentList :=
  exists_arb_program_of_spec (by omega) edmondsProg_realizes edmondsProg_spec

/-- Materialized-table Chu–Liu/Edmonds minimum-cost spanning out-arborescence runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 1) * I.maxAbsCost + 32 * (I.n + 1) ^ 2` bounds word values and addresses,
so `w` of order `log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
theorem exists_edmondsOut_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) ArborescenceInput.expectedOutParentList :=
  exists_arb_program_of_spec (by omega) edmondsOutProg_realizes edmondsOutProg_spec

/-- Maximum-weight branching via this formalization's super-root reduction to rooted spanning
in-arborescence (`CslibFrontier.Algorithms.Lean.Arborescence.Branching`) runs in at most
`C * (I.n + 1) ^ 3` instructions on the deterministic width-blind standard-basis Word-RAM at every
word width `w` satisfying `Fits w I.wordBound` (i.e., `I.wordBound < 2 ^ w`, where
`I.wordBound = 4 * (I.n + 2) * I.maxAbsWeight + 32 * (I.n + 2) ^ 2` bounds word values and
addresses, so `w` of order `log(I.n + 2) + log(I.maxAbsWeight + 2)` bits suffices). -/
theorem exists_optimumBranching_program :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧
      prog.ComputesListInTime (fun _ I => I.encode) (fun I _ => C * (I.n + 1) ^ 3)
        (fun I w => Fits w I.wordBound) BranchingInput.expectedParentList := by
  obtain ⟨r, C₁, pc, prog, hnw, frontier, _, he⟩ :=
    optimumBranchingProg_realizes.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, 80 * C₁ + 1, prog, hnw, fun I w hwb _ => ?_⟩
  obtain ⟨hfit_len, hin_fits⟩ := inputFits_branching_encode I I.natAbs_weight_le_maxAbsWeight hwb
  have hspec := optimumBranchingProg_spec I I.natAbs_weight_le_maxAbsWeight hwb
  exact executesList_of_client_spec he I.n I.encode I.expectedParentList
    (by rintro ⟨_ | _, h⟩; exacts [rfl, by omega])
    (by simp [BranchingInput.encode]) hfit_len hin_fits hspec.1 hspec.2.1
    (by
      have hmc := hspec.2.2.1
      have hpos : 1 ≤ (I.n + 1) ^ 3 := Nat.one_le_pow 3 (I.n + 1) (Nat.succ_pos _)
      have hsq : (I.n + 1) ^ 2 ≤ (I.n + 1) ^ 3 :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
      have hlin : I.n + 1 ≤ (I.n + 1) ^ 3 := by
        simpa using Nat.pow_le_pow_right (Nat.succ_pos I.n) (show 1 ≤ 3 by decide)
      linarith [hmc, hpos, hsq, hlin])
    hspec.2.2.2.1 hspec.2.2.2.2

end

end Cslib.Algorithms.WordRAM.Arborescence
