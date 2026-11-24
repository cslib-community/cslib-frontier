/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.IterativeCompression.OddCycleTransversal
public import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Odd cycle transversal by iterative compression on the Word-RAM

Implements the iterative-compression odd-cycle-transversal algorithm of Reed, Smith and Vetta
`[ReedSmithVetta2004]` with Hüffner's three-way compression branching `[Hueffner2009]` and
`[CyganEtAl2015, Section 4.4]` as a single uniform flat program over `Cslib.WordRAM.Basis.exact`.
`Basis.exact` supplies unit-cost multiplication for the `n × n` adjacency matrix and
`(2n + 2) × (2n + 2)` split-network flow matrix index arithmetic.

## Overview

Given an `n`-vertex simple graph `G` serialized in `State.init (encodeInput G k)` (`n :: k ::
encodeAdjMatrix G`), the program allocates workspace up to `octWorkspace n = 5 * n ^ 2 + 21 * n +
11` and maintains a `0`/`1` indicator of an odd cycle transversal `S` of `prefixGraph G m` (`|S| ≤
k`) at `sepAddr n 0 .. sepAddr n (n - 1)` together with a proper Boolean colouring off `S` at
`colAddr n 0 .. colAddr n (n - 1)`:

1. **Outer vertex-addition loop (`octStep`, `m = 0 .. n - 1`):** forms `W = S ∪ {m}` and compacts
   `W` into `wListBase`. When `|W| ≤ k`, `W` is accepted directly; otherwise `|W| = k + 1` and
   `compressProg` enumerates all `3 ^ |W|` three-way guesses on `W` via a base-3 odometer.
2. **Compression leaf (`leafProg`) and unit-capacity vertex-split max-flow (`minSepProg`):** checks
   properness on the kept part of `W`, marks keep and flip terminals outside `W`, runs `n` rounds of
   layered BFS + unit augmentation on the `(2n + 2)`-vertex split network, extracts the minimum
   vertex separator from the final residual reachable cut, and commits `D ∪ X` and the updated
   colouring when `|D| + |X| ≤ k`.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeAdjMatrix`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeInput`: row-major `0`/`1` adjacency matrix and
  prefixed input word list `n :: k :: encodeAdjMatrix G`, with the layout lemmas
  `length_encodeAdjMatrix`, `length_encodeInput` and `getElem_encodeAdjMatrix`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.sepAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.colAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.octWorkspace`: output transversal/colouring cell
  addresses and total memory frontier `5 * n ^ 2 + 21 * n + 11`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance.encode`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance.Yes`: packaged decision instances,
  encoding, and yes-set for `UniformDecidableInTime`.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.exists_oct_program`: a single uniform flat program
  over `Basis.exact` decides whether `G` has an odd cycle transversal of size at most `k` within
  `C * 3 ^ k * (n + 1) ^ 5` instructions whenever `Fits w (octWorkspace n)` and `Fits w k`, and on
  yes-instances materializes a valid transversal of size `≤ k` and a proper `2`-colouring off it in
  final machine memory.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.uniformDecidableInTime_oct`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.uniformDecidableInTimeLogWord_oct`: uniform FPT
  `O(3 ^ k · n ^ 5)` decision certificates under explicit workspace fit and under the
  transdichotomous logarithmic word-size convention.

## References

* [B. Reed, K. Smith, A. Vetta, *Finding odd cycle transversals*][ReedSmithVetta2004]
* [F. Hüffner, *Algorithm engineering for optimal graph bipartization*][Hueffner2009]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph SimpleGraph.OddCycleTransversal
open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-! ### Input encoding and workspace layout -/

/-- Row-major `n * n`-word `0`/`1` adjacency matrix of `G : SimpleGraph (Fin n)`. -/
@[expose] def encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  List.ofFn fun idx : Fin (n * n) =>
    if G.Adj ⟨idx.1 / n, Nat.div_lt_of_lt_mul idx.2⟩
        ⟨idx.1 % n, Nat.mod_lt _ (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt idx.2))⟩ then 1 else 0

/-- Word-RAM input word list `n :: k :: encodeAdjMatrix G`. -/
@[expose] def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    List ℕ :=
  n :: k :: encodeAdjMatrix G

@[simp]
theorem length_encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (encodeAdjMatrix G).length = n * n := by
  simp [encodeAdjMatrix]

@[simp]
theorem length_encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (encodeInput G k).length = 2 + n * n := by
  simp only [encodeInput, List.length_cons, length_encodeAdjMatrix]
  omega

theorem getElem_encodeAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    (encodeAdjMatrix G)[u.1 * n + v.1]'(by
      rw [length_encodeAdjMatrix]; nlinarith [u.2, v.2]) =
      if G.Adj u v then 1 else 0 := by
  simp only [encodeAdjMatrix, List.getElem_ofFn]
  have hu : u.1 * n + v.1 = v.1 + n * u.1 := by ring
  have hn_pos : 0 < n := Nat.zero_lt_of_lt u.2
  have hdiv : (u.1 * n + v.1) / n = u.1 := by
    rw [hu, Nat.add_mul_div_left _ _ hn_pos]
    simp [Nat.div_eq_of_lt v.2]
  have hmod : (u.1 * n + v.1) % n = v.1 := by
    rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.2]
  have h1 : G.Adj ⟨(u.1 * n + v.1) / n,
      Nat.div_lt_of_lt_mul (by nlinarith [u.2, v.2] : u.1 * n + v.1 < n * n)⟩
      ⟨(u.1 * n + v.1) % n, Nat.mod_lt _ hn_pos⟩ ↔ G.Adj u v := by
    refine Iff.of_eq ?_
    congr 1
    · exact Fin.ext hdiv
    · exact Fin.ext hmod
  simp only [h1]

/-- Number of vertices `n + n + 2` in the vertex-split network of an `n`-vertex graph. -/
private abbrev splitCount (n : ℕ) : ℕ := n + n + 2

/-- Output address storing the `0`/`1` transversal indicator of vertex `v` (`3 + n * n + v`). -/
@[expose] def sepAddr (n v : ℕ) : ℕ := 3 + n * n + v

/-- Output address storing the `0`/`1` proper colouring bit of vertex `v`
(`3 + n * n + n + v`). -/
@[expose] def colAddr (n v : ℕ) : ℕ := 3 + n * n + n + v

private abbrev sepBase (n : ℕ) : ℕ := 3 + n * n
private abbrev colBase (n : ℕ) : ℕ := 3 + n * n + n
private abbrev wBase (n : ℕ) : ℕ := 3 + n * n + 2 * n
private abbrev wListBase (n : ℕ) : ℕ := 3 + n * n + 3 * n
private abbrev digitBase (n : ℕ) : ℕ := 3 + n * n + 4 * n
private abbrev guessBase (n : ℕ) : ℕ := 3 + n * n + 5 * n
private abbrev keepBase (n : ℕ) : ℕ := 3 + n * n + 6 * n
private abbrev flipBase (n : ℕ) : ℕ := 3 + n * n + 7 * n
private abbrev flowBase (n : ℕ) : ℕ := 3 + n * n + 8 * n
private abbrev distBase (n : ℕ) : ℕ := flowBase n + splitCount n * splitCount n
private abbrev parBase (n : ℕ) : ℕ := distBase n + splitCount n
private abbrev sepOutBase (n : ℕ) : ℕ := parBase n + splitCount n

/-- Total scratch words allocated past `3 + n * n`. -/
private abbrev octScratch (n : ℕ) : ℕ :=
  9 * n + splitCount n * splitCount n + 2 * splitCount n

/-- Total memory frontier `5 * (n * n) + 21 * n + 11` (`= 3 + n * n + octScratch n`) used by the
Word-RAM odd-cycle-transversal solver. -/
@[expose] def octWorkspace (n : ℕ) : ℕ :=
  5 * (n * n) + 21 * n + 11

private theorem frontier_add_octScratch (n : ℕ) :
    3 + n * n + octScratch n = octWorkspace n := by
  unfold octWorkspace octScratch splitCount
  ring

private theorem splitCount_sq (n : ℕ) :
    (n + n + 2) * (n + n + 2) = 4 * (n * n) + 8 * n + 4 := by
  ring

/-! ### Client reduction and frame helpers for `Memory.Prog` -/

attribute [local client_simps] runClient_read runClient_write clientState_map

private theorem preservesAt_iterate_fst {a : ℕ} {δ β : Type}
    {body : δ × (ℕ × β) → Memory.Prog (ℕ × β)} {d : δ}
    {m : ℕ} (b₀ : β) (hstep : ∀ i < m, ∀ b, PreservesAt a (body (d, (i, b))) ∧
      ∀ s, ((Memory.spec 0).clientResult s (body (d, (i, b)))).1 = i + 1) :
    PreservesAt a (iterate body d m (0, b₀)) := fun s =>
  (iterate_invariant_of body d (fun rem (ib : ℕ × β) t => ib.1 + rem = m ∧ t.mem a = s.mem a)
    (fun rem ib t ⟨hsum, hmem⟩ => by
      obtain ⟨hp, hr⟩ := hstep ib.1 (by omega) ib.2
      exact ⟨by rw [hr]; omega, (hp t).trans hmem⟩)
    ⟨Nat.zero_add _, rfl⟩).2

/-! ### Array fill and copy helpers -/

private def fillStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + d.2) d.1.2
  pure (d.2 + 1)

private def fillRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillStep d.1 d.2 0
  pure ()

private theorem fillStep_realizes :
    Realizes .exact fillStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.2 + 1)) (fun _ _ => 0) := by
  unfold fillStep
  realize
  · exact h.1
  · exact h.2

private theorem fillRange_realizes :
    Realizes .exact fillRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (d.1.1 + d.2)) (fun _ _ => 0) := by
  unfold fillRange
  realize [fillStep_realizes]
  refine iterationSafe_of_stepInv _ _ w d
    (fun rem (idx : ℕ) _ => idx + rem = d.2 ∧ Fits w (d.1.1 + d.2)) ?_ ⟨Nat.zero_add _, h⟩
  intro rem idx t ⟨hsum, hfit⟩
  dsimp only [fillStep]
  simp only [client_simps]
  exact ⟨⟨by apply hfit.of_le; omega, by apply hfit.of_le; omega⟩, by omega, hfit⟩

private theorem preservesAt_fillRange {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (hout : a < d.1.1 ∨ d.1.1 + d.2 ≤ a) :
    PreservesAt a (fillRange d) := fun s => by
  unfold fillRange
  rw [StateTransitionSpec.clientState_bind]
  change ((Memory.spec 0).clientState s (iterate fillStep d.1 d.2 0)).mem a = s.mem a
  refine iterate_invariant_of fillStep d.1
    (fun rem (idx : ℕ) t => idx + rem = d.2 ∧ t.mem a = s.mem a)
    (fun rem idx t ⟨hsum, hmem⟩ => ?_) ⟨Nat.zero_add _, rfl⟩ |>.2
  unfold fillStep
  simp only [client_simps]
  exact ⟨by omega, (Function.update_of_ne (by omega) _ t.mem).trans hmem⟩

private def copyStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let v ← Memory.read (d.1.1 + d.2)
  Memory.write (d.1.2 + d.2) v
  pure (d.2 + 1)

private def copyRange (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let _ ← iterate copyStep d.1 d.2 0
  pure ()

private theorem copyStep_realizes :
    Realizes .exact copyStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.1.2 + d.2) ∧ Fits w (d.2 + 1))
      (fun _ _ => 0) := by
  unfold copyStep
  realize
  · exact h.1
  · exact h.2.1
  · exact h.2.2

private theorem copyRange_realizes :
    Realizes .exact copyRange (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (d.1.1 + d.2) ∧ Fits w (d.1.2 + d.2)) (fun _ _ => 0) := by
  unfold copyRange
  realize [copyStep_realizes]
  refine iterationSafe_of_stepInv _ _ w d
    (fun rem (idx : ℕ) _ => idx + rem = d.2 ∧ Fits w (d.1.1 + d.2) ∧ Fits w (d.1.2 + d.2))
    ?_ ⟨Nat.zero_add _, h.1, h.2⟩
  intro rem idx t ⟨hsum, hf1, hf2⟩
  dsimp only [copyStep]
  simp only [client_simps]
  exact ⟨⟨by apply hf1.of_le; omega, by apply hf2.of_le; omega, by apply hf1.of_le; omega⟩,
    by omega, hf1, hf2⟩

/-! ### Split-network capacity, residual capacity, BFS, and unit augmentation -/

private def readSplitCap (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  if d.1.2 = 0 then
    if 2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
      let a ← Memory.read (keepBase d.1.1.1 + (d.2 - 2))
      if a = 1 then pure (d.1.1.1 + 1) else pure 0
    else pure 0
  else if d.2 = 1 then
    if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 then
      let b ← Memory.read (flipBase d.1.1.1 + (d.1.2 - (d.1.1.1 + 2)))
      if b = 1 then pure (d.1.1.1 + 1) else pure 0
    else pure 0
  else if 2 ≤ d.1.2 ∧ d.1.2 < d.1.1.1 + 2 then
    if d.2 = d.1.2 + d.1.1.1 then
      let z ← Memory.read (wBase d.1.1.1 + (d.1.2 - 2))
      if z = 0 then pure 1 else pure 0
    else pure 0
  else if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 ∧
      2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
    let u := d.1.2 - (d.1.1.1 + 2)
    let v := d.2 - 2
    if u < d.1.1.2 ∧ v < d.1.1.2 then
      let e ← Memory.read (3 + u * d.1.1.1 + v)
      if e = 1 then pure (d.1.1.1 + 1) else pure 0
    else pure 0
  else pure 0

private theorem readSplitCap_realizes :
    Realizes .exact readSplitCap (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold readSplitCap
  realize
  all_goals
    obtain ⟨hw, hx, hy⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, splitCount, keepBase, flipBase, wBase] at *
    first
    | omega
    | (apply hw.of_le
       first
       | omega
       | (have hu : d.1.2 - (d.1.1.1 + 2) < d.1.1.1 := by omega
          have hmul : (d.1.2 - (d.1.1.1 + 2)) * d.1.1.1 < d.1.1.1 * d.1.1.1 :=
            Nat.mul_lt_mul_of_pos_right hu (by omega)
          omega))

private theorem clientState_readSplitCap (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readSplitCap d) = s := by
  unfold readSplitCap
  rw [clientState_bind_read]
  dsimp only
  split_ifs <;> try rfl
  all_goals rw [clientState_bind_read]; split_ifs <;> rfl

private theorem preservesAt_readSplitCap (a : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    PreservesAt a (readSplitCap d) := fun s => by
  rw [clientState_readSplitCap]

private def readResCap (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let cap ← readSplitCap d
  let M := splitCount d.1.1.1
  let fxy ← Memory.read (flowBase d.1.1.1 + d.1.2 * M + d.2)
  let fyx ← Memory.read (flowBase d.1.1.1 + d.2 * M + d.1.2)
  if cap ≤ d.1.1.1 + 1 ∧ fxy ≤ cap ∧ fyx ≤ d.1.1.1 + 1 then
    pure ((cap - fxy) + fyx)
  else pure 0

private theorem readResCap_realizes :
    Realizes .exact readResCap (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold readResCap
  realize [readSplitCap_realizes]
  all_goals
    obtain ⟨hw, hx, hy⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, flowBase, splitCount] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

private theorem preservesAt_readResCap (a : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    PreservesAt a (readResCap d) := by
  unfold readResCap
  refine preservesAt_bind (preservesAt_readSplitCap a d) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

private def bfsInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1.1
  let m := d.1.1.1.2
  let layer := d.1.1.2
  let u := d.1.2
  let v := d.2
  let M := splitCount n
  let dv ← Memory.read (distBase n + v)
  let rc ← readResCap (((n, m), u), v)
  if dv = M ∧ 0 < rc then
    Memory.write (distBase n + v) (layer + 1)
    Memory.write (parBase n + v) u
    pure (v + 1)
  else
    pure (v + 1)

private theorem bfsInnerStep_realizes :
    Realizes .exact bfsInnerStep (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.1.1.2 < splitCount d.1.1.1.1 ∧
        d.1.2 < splitCount d.1.1.1.1 ∧ d.2 < splitCount d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold bfsInnerStep
  realize [readResCap_realizes]
  all_goals
    obtain ⟨hw, hl, hu, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, parBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1.1.1.1
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_bfsInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsInnerStep d) = d.2 + 1 := by
  unfold bfsInnerStep
  rw [clientResult_bind_read, clientResult_bind]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private def bfsMidStep (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let m := d.1.1.2
  let layer := d.1.2
  let u := d.2
  let du ← Memory.read (distBase n + u)
  if du = layer then
    let _ ← iterate bfsInnerStep (((n, m), layer), u) (splitCount n) 0
    pure (u + 1)
  else
    pure (u + 1)

private theorem bfsMidStep_realizes :
    Realizes .exact bfsMidStep (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 < splitCount d.1.1.1 ∧
        d.2 < splitCount d.1.1.1)
      (fun _ _ => 0) := by
  unfold bfsMidStep
  realize [bfsInnerStep_realizes]
  all_goals
    obtain ⟨hw, hl, hu⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1.1.1
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = splitCount d.1.1.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp -failIfUnchanged only [octWorkspace, splitCount] at *
  refine ⟨⟨hw, hl, hu, by omega⟩, ?_⟩
  rw [clientResult_bfsInnerStep]
  omega

private theorem clientResult_bfsMidStep (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bfsMidStep d) = d.2 + 1 := by
  unfold bfsMidStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

private def bfsLayerStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1
  let m := d.1.2
  let layer := d.2
  let _ ← Memory.read 0
  let _ ← iterate bfsMidStep ((n, m), layer) (splitCount n) 0
  pure (layer + 1)

private theorem bfsLayerStep_realizes :
    Realizes .exact bfsLayerStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 < splitCount d.1.1)
      (fun _ _ => 0) := by
  unfold bfsLayerStep
  realize [bfsMidStep_realizes]
  all_goals
    obtain ⟨hw, hl⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, splitCount] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (u : ℕ) _ => u + rem = splitCount d.1.1) ?_ (Nat.zero_add _)
  intro rem u t hsum
  dsimp -failIfUnchanged only [octWorkspace, splitCount] at *
  refine ⟨⟨hw, hl, by omega⟩, ?_⟩
  rw [clientResult_bfsMidStep]
  omega

private def bfsProg (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n := d.1
  let M := splitCount n
  fillRange ((distBase n, M), M)
  Memory.write (distBase n) 0
  Memory.write (parBase n) 0
  let _ ← iterate bfsLayerStep d (M - 1) 0
  pure ()

private theorem bfsProg_realizes :
    Realizes .exact bfsProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold bfsProg
  realize [fillRange_realizes, bfsLayerStep_realizes]
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, parBase, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    try omega
    try (apply h.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (layer : ℕ) _ => layer + rem = splitCount d.1 - 1) ?_ (Nat.zero_add _)
  intro rem layer t hsum
  dsimp -failIfUnchanged only [bfsLayerStep, octWorkspace, splitCount] at *
  refine ⟨⟨h, by omega⟩, ?_⟩
  simp only [client_simps]
  omega

private theorem preservesAt_bfsProg {a : ℕ} {d : ℕ × ℕ}
    (ha : a < distBase d.1 ∨ parBase d.1 + splitCount d.1 ≤ a) :
    PreservesAt a (bfsProg d) := by
  have h1 : a < distBase d.1 ∨ distBase d.1 + splitCount d.1 ≤ a := by
    dsimp only [parBase] at ha; omega
  unfold bfsProg
  refine preservesAt_bind (preservesAt_fillRange h1) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by dsimp only [parBase, splitCount] at ha ⊢; omega))
    fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by dsimp only [parBase, splitCount] at ha ⊢; omega))
    fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_nat fun layer _ => ⟨?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold bfsLayerStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_iterate_nat fun u _ => ⟨?_, fun s => ?_⟩)
      fun _ => preservesAt_pure _ _
    · unfold bfsMidStep
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_iterate_nat fun v hv => ⟨?_, fun s => ?_⟩)
        fun _ => preservesAt_pure _ _
      · unfold bfsInnerStep
        refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
        refine preservesAt_bind (preservesAt_readResCap a _) fun _ => ?_
        refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
        refine preservesAt_bind (preservesAt_write _
          (by dsimp only [parBase, distBase, splitCount] at ha hv ⊢; omega)) fun _ => ?_
        refine preservesAt_bind (preservesAt_write _
          (by dsimp only [parBase, distBase, splitCount] at ha hv ⊢; omega))
          fun _ => preservesAt_pure _ _
      · exact clientResult_bfsInnerStep _ s
    · exact clientResult_bfsMidStep _ s
  · unfold bfsLayerStep
    simp only [client_simps]

private def pushUnitStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let cur := d.2
  let M := splitCount n
  let _ ← Memory.read 0
  if cur < M then
    let u ← Memory.read (parBase n + cur)
    if u < M then
      let f_rev ← Memory.read (flowBase n + cur * M + u)
      if 0 < f_rev then
        Memory.write (flowBase n + cur * M + u) (f_rev - 1)
        pure u
      else
        let f_fwd ← Memory.read (flowBase n + u * M + cur)
        if f_fwd ≤ n then
          Memory.write (flowBase n + u * M + cur) (f_fwd + 1)
          pure u
        else pure u
    else pure 0
  else pure 0

private theorem pushUnitStep_realizes :
    Realizes .exact pushUnitStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold pushUnitStep
  realize
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, parBase, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply h.of_le; first | omega | nlinarith)

private theorem preservesAt_pushUnitStep {a : ℕ} {d : ℕ × ℕ}
    (ha : a < flowBase d.1 ∨ distBase d.1 ≤ a) :
    PreservesAt a (pushUnitStep d) := by
  unfold pushUnitStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  by_cases hcur : d.2 < splitCount d.1
  · rw [ite_eq_left hcur]
    refine preservesAt_bind (preservesAt_read _ _) fun u => ?_
    by_cases hu : u < splitCount d.1
    · rw [ite_eq_left hu]
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ ?_
      · refine preservesAt_bind (preservesAt_write _ ?_) fun _ => preservesAt_pure _ _
        dsimp only [distBase] at ha
        have : d.2 * splitCount d.1 + u < splitCount d.1 * splitCount d.1 := by nlinarith
        omega
      · refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
        refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
        refine preservesAt_bind (preservesAt_write _ ?_) fun _ => preservesAt_pure _ _
        dsimp only [distBase] at ha
        have : u * splitCount d.1 + d.2 < splitCount d.1 * splitCount d.1 := by nlinarith
        omega
    · rw [ite_eq_right hu]; exact preservesAt_pure _ _
  · rw [ite_eq_right hcur]; exact preservesAt_pure _ _

private def augRoundStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1
  let m := d.1.2
  bfsProg (n, m)
  let M := splitCount n
  let d1 ← Memory.read (distBase n + 1)
  if d1 < M then
    let _ ← iterate pushUnitStep n d1 1
    pure (d.2 + 1)
  else
    pure (d.2 + 1)

private theorem augRoundStep_realizes :
    Realizes .exact augRoundStep (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 < d.1.1) (fun _ _ => 0) := by
  unfold augRoundStep
  realize [bfsProg_realizes, pushUnitStep_realizes]
  all_goals
    obtain ⟨hw, hr⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, distBase, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1.1
    try exact hw
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _ (fun _ (_ : ℕ) _ => True) ?_ trivial
  intro _ _ _ _
  exact ⟨hw, trivial⟩

private theorem clientResult_augRoundStep (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (augRoundStep d) = d.2 + 1 := by
  unfold augRoundStep
  rw [clientResult_bind, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

private def extractSepStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let v := d.2.1
  let count := d.2.2
  let M := splitCount n
  let z ← Memory.read (wBase n + v)
  let din ← Memory.read (distBase n + (v + 2))
  let dout ← Memory.read (distBase n + (v + n + 2))
  if z = 0 ∧ din < M ∧ dout = M then
    Memory.write (sepOutBase n + v) 1
    pure (v + 1, count + 1)
  else
    Memory.write (sepOutBase n + v) 0
    pure (v + 1, count)

private theorem extractSepStep_realizes :
    Realizes .exact extractSepStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold extractSepStep
  realize
  all_goals
    obtain ⟨hw, hv, hc⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, distBase, sepOutBase, parBase, flowBase,
      splitCount] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_extractSepStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (extractSepStep d)).1 = d.2.1 + 1 ∧
      ((Memory.spec 0).clientResult s (extractSepStep d)).2 ≤ d.2.2 + 1 := by
  unfold extractSepStep
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure] <;> exact ⟨trivial, by omega⟩

private def minSepProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let M := splitCount n
  fillRange ((flowBase n, 0), M * M)
  let _ ← iterate augRoundStep d n 0
  bfsProg d
  let res ← iterate extractSepStep n n (0, 0)
  pure res.2

private theorem minSepProg_realizes :
    Realizes .exact minSepProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1)) (fun _ _ => 0) := by
  unfold minSepProg
  realize [fillRange_realizes, augRoundStep_realizes, bfsProg_realizes, extractSepStep_realizes]
  all_goals
    dsimp -failIfUnchanged only [octWorkspace, flowBase, splitCount] at *
    have hsq := splitCount_sq d.1
    try exact h
    try (apply h.of_le; omega)
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (r : ℕ) _ => r + rem = d.1) ?_ (Nat.zero_add _)
    intro rem r t hsum
    dsimp only
    refine ⟨⟨h, by omega⟩, ?_⟩
    rw [clientResult_augRoundStep]
    omega
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (vc : ℕ × ℕ) _ => vc.1 + rem = d.1 ∧ vc.2 ≤ vc.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
    intro rem vc t ⟨hsum, hc⟩
    dsimp only
    refine ⟨⟨h, by omega, hc⟩, ?_⟩
    obtain ⟨h1, h2⟩ := clientResult_extractSepStep (d.1, vc) t
    dsimp only at h1 h2
    exact ⟨by omega, by omega⟩

private theorem preservesAt_minSepProg {a : ℕ} {d : ℕ × ℕ} (ha : a < flowBase d.1) :
    PreservesAt a (minSepProg d) := by
  unfold minSepProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun r => ?_) _ _) fun _ => ?_
  · unfold augRoundStep
    refine preservesAt_bind (preservesAt_bfsProg (Or.inl (by dsimp only [distBase]; omega)))
      fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
    refine preservesAt_bind
      (preservesAt_iterate (fun cur => preservesAt_pushUnitStep (Or.inl ha)) _ _)
      fun _ => preservesAt_pure _ _
  · refine preservesAt_bind (preservesAt_bfsProg (Or.inl (by dsimp only [distBase]; omega)))
      fun _ => ?_
    refine preservesAt_bind (preservesAt_iterate (fun vc => ?_) _ _) fun _ => preservesAt_pure _ _
    unfold extractSepStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ ?_ <;>
      exact preservesAt_bind
        (preservesAt_write _
          (by dsimp only [sepOutBase, parBase, distBase, flowBase] at ha ⊢; omega))
        fun _ => preservesAt_pure _ _

/-! ### Compression leaf, base-3 odometer, and outer iterative compression -/

private def buildWListStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let v := d.2.1
  let L := d.2.2
  let wv ← Memory.read (wBase n + v)
  if wv = 1 then
    Memory.write (wListBase n + L) v
    pure (v + 1, L + 1)
  else
    pure (v + 1, L)

private theorem buildWListStep_realizes :
    Realizes .exact buildWListStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold buildWListStep
  realize
  all_goals
    obtain ⟨hw, hv, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, wListBase] at *
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_buildWListStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (buildWListStep d)).1 = d.2.1 + 1 ∧
      ((Memory.spec 0).clientResult s (buildWListStep d)).2 ≤ d.2.2 + 1 := by
  unfold buildWListStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure] <;> exact ⟨trivial, by omega⟩

private def buildWProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let m := d.2
  copyRange ((sepBase n, wBase n), n)
  Memory.write (wBase n + m) 1
  let res ← iterate buildWListStep n n (0, 0)
  pure res.2

private theorem buildWProg_realizes :
    Realizes .exact buildWProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold buildWProg
  realize [copyRange_realizes, buildWListStep_realizes]
  all_goals
    obtain ⟨hw, hm⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, sepBase, wBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (vL : ℕ × ℕ) _ => vL.1 + rem = d.1 ∧ vL.2 ≤ vL.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
  intro rem vL t ⟨hsum, hL⟩
  dsimp only
  refine ⟨⟨hw, by omega, hL⟩, ?_⟩
  obtain ⟨h1, h2⟩ := clientResult_buildWListStep (d.1, vL) t
  dsimp only at h1 h2
  exact ⟨by omega, by omega⟩

private def unpackStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let j := d.2
  let wv ← Memory.read (wListBase n + j)
  let dg ← Memory.read (digitBase n + j)
  if wv < n ∧ dg ≤ 2 then
    Memory.write (guessBase n + wv) dg
    pure (j + 1)
  else
    pure (j + 1)

private theorem unpackStep_realizes :
    Realizes .exact unpackStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold unpackStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase, guessBase] at *
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_unpackStep (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (unpackStep d) = d.2 + 1 := by
  unfold unpackStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private def unpackGuessProg (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n := d.1
  let L := d.2
  fillRange ((guessBase n, 0), n)
  let _ ← iterate unpackStep n L 0
  pure ()

private theorem unpackGuessProg_realizes :
    Realizes .exact unpackGuessProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold unpackGuessProg
  realize [fillRange_realizes, unpackStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, guessBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (j : ℕ) _ => j + rem = d.2) ?_ (Nat.zero_add _)
  intro rem j t hsum
  dsimp only
  refine ⟨⟨hw, by omega⟩, ?_⟩
  rw [clientResult_unpackStep]
  omega

private theorem preservesAt_unpackGuessProg {a : ℕ} {d : ℕ × ℕ} (ha : a < guessBase d.1) :
    PreservesAt a (unpackGuessProg d) := by
  unfold unpackGuessProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun j => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold unpackStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind
    (preservesAt_write _ (by dsimp only [guessBase] at ha ⊢; omega))
    fun _ => preservesAt_pure _ _

private def properInnerStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1.1.1.1
  let m := d.1.1.1.2
  let u := d.1.1.2
  let du := d.1.2
  let j := d.2.1
  let ok := d.2.2
  let v ← Memory.read (wListBase n + j)
  let dv ← Memory.read (digitBase n + j)
  if u < n ∧ v < n ∧ u < m ∧ v < m ∧ 0 < dv ∧ du = dv then
    let e ← Memory.read (3 + u * n + v)
    if e = 1 then pure (j + 1, 0) else pure (j + 1, ok)
  else
    pure (j + 1, ok)

private theorem properInnerStep_realizes :
    Realizes .exact properInnerStep
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.2.1 < d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold properInnerStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

private theorem clientResult_properInnerStep_fst (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (properInnerStep d)).1 = d.2.1 + 1 := by
  unfold properInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind_read]; split_ifs <;> rfl
  · rfl

private def properOuterStep (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1.1.1
  let m := d.1.1.2
  let L := d.1.2
  let i := d.2.1
  let ok := d.2.2
  let u ← Memory.read (wListBase n + i)
  let du ← Memory.read (digitBase n + i)
  if u < n ∧ 0 < du then
    let res ← iterate properInnerStep (((n, m), u), du) L (0, ok)
    pure (i + 1, res.2)
  else
    pure (i + 1, ok)

private theorem properOuterStep_realizes :
    Realizes .exact properOuterStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 ≤ d.1.1.1 ∧ d.2.1 < d.1.2)
      (fun _ _ => 0) := by
  unfold properOuterStep
  realize [properInnerStep_realizes]
  all_goals
    obtain ⟨hw, hL, hi⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (jok : ℕ × ℕ) _ => jok.1 + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem jok t hsum
  dsimp only
  refine ⟨⟨hw, by omega⟩, ?_⟩
  rw [clientResult_properInnerStep_fst]
  dsimp only
  omega

private theorem clientResult_properOuterStep_fst (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (properOuterStep d)).1 = d.2.1 + 1 := by
  unfold properOuterStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

private def checkProperProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate properOuterStep d d.2 (0, 1)
  pure res.2

private theorem checkProperProg_realizes :
    Realizes .exact checkProperProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 ≤ d.1.1) (fun _ _ => 0) := by
  unfold checkProperProg
  realize [properOuterStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (iok : ℕ × ℕ) _ => iok.1 + rem = d.2) ?_ (Nat.zero_add _)
  intro rem iok t hsum
  dsimp only
  refine ⟨⟨hw, hL, by omega⟩, ?_⟩
  rw [clientResult_properOuterStep_fst]
  dsimp only
  omega

private theorem preservesAt_checkProperProg (a : ℕ) (d : (ℕ × ℕ) × ℕ) :
    PreservesAt a (checkProperProg d) := by
  unfold checkProperProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun iok => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold properOuterStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_iterate (fun jok => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold properInnerStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

private def termInnerStep (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let m := d.1.1.2
  let v := d.1.2.1
  let cv := d.1.2.2
  let j := d.2
  let u ← Memory.read (wListBase n + j)
  let du ← Memory.read (digitBase n + j)
  if u < n ∧ v < n ∧ u < m ∧ v < m ∧ 0 < du then
    let e ← Memory.read (3 + u * n + v)
    if e = 1 then
      if du - 1 = cv then
        Memory.write (flipBase n + v) 1
        pure (j + 1)
      else
        Memory.write (keepBase n + v) 1
        pure (j + 1)
    else pure (j + 1)
  else pure (j + 1)

private theorem termInnerStep_realizes :
    Realizes .exact termInnerStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 < d.1.1.1)
      (fun _ _ => 0) := by
  unfold termInnerStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wListBase, digitBase, flipBase, keepBase] at *
    first | omega | (apply hw.of_le; first | omega | nlinarith)

private theorem clientResult_termInnerStep (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (termInnerStep d) = d.2 + 1 := by
  unfold termInnerStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> try rfl
  all_goals
    rw [clientResult_bind_read]
    split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private def termOuterStep (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let m := d.1.1.2
  let L := d.1.2
  let v := d.2
  let zv ← Memory.read (wBase n + v)
  let cv ← Memory.read (colBase n + v)
  if zv = 0 ∧ v < m then
    let _ ← iterate termInnerStep ((n, m), (v, cv)) L 0
    pure (v + 1)
  else
    pure (v + 1)

private theorem termOuterStep_realizes :
    Realizes .exact termOuterStep
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.1.2 ≤ d.1.1.1 ∧ d.2 < d.1.1.1)
      (fun _ _ => 0) := by
  unfold termOuterStep
  realize [termInnerStep_realizes]
  all_goals
    obtain ⟨hw, hL, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, colBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (j : ℕ) _ => j + rem = d.1.2) ?_ (Nat.zero_add _)
  intro rem j t hsum
  dsimp only
  refine ⟨⟨hw, by omega⟩, ?_⟩
  rw [clientResult_termInnerStep]
  omega

private theorem clientResult_termOuterStep (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (termOuterStep d) = d.2 + 1 := by
  unfold termOuterStep
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

private def buildTerminalsProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  let n := d.1.1
  fillRange ((keepBase n, 0), n)
  fillRange ((flipBase n, 0), n)
  let _ ← iterate termOuterStep d n 0
  pure ()

private theorem buildTerminalsProg_realizes :
    Realizes .exact buildTerminalsProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2 ≤ d.1.1) (fun _ _ => 0) := by
  unfold buildTerminalsProg
  realize [fillRange_realizes, termOuterStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, keepBase, flipBase] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = d.1.1) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only
  refine ⟨⟨hw, hL, by omega⟩, ?_⟩
  rw [clientResult_termOuterStep]
  omega

private theorem preservesAt_buildTerminalsProg {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (ha : a < keepBase d.1.1) :
    PreservesAt a (buildTerminalsProg d) := by
  have ha_flip : a < flipBase d.1.1 := by dsimp only [keepBase, flipBase] at ha ⊢; omega
  unfold buildTerminalsProg
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_fillRange (Or.inl ha_flip)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun v => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold termOuterStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_iterate (fun j => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold termInnerStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_ite _ ?_ ?_ <;>
    exact preservesAt_bind
      (preservesAt_write _ (by dsimp only [keepBase, flipBase] at ha ⊢; omega))
      fun _ => preservesAt_pure _ _

private def countDelStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let j := d.2.1
  let cnt := d.2.2
  let dj ← Memory.read (digitBase n + j)
  if dj = 0 then pure (j + 1, cnt + 1) else pure (j + 1, cnt)

private theorem countDelStep_realizes :
    Realizes .exact countDelStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1 ∧ d.2.2 ≤ d.2.1)
      (fun _ _ => 0) := by
  unfold countDelStep
  realize
  all_goals
    obtain ⟨hw, hj, hc⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase] at *
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_countDelStep (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (countDelStep d)).1 = d.2.1 + 1 ∧
      ((Memory.spec 0).clientResult s (countDelStep d)).2 ≤ d.2.2 + 1 := by
  unfold countDelStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_pure] <;> exact ⟨trivial, by omega⟩

private def countDelProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate countDelStep d.1 d.2 (0, 0)
  pure res.2

private theorem countDelProg_realizes :
    Realizes .exact countDelProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold countDelProg
  realize [countDelStep_realizes]
  obtain ⟨hw, hL⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (jc : ℕ × ℕ) _ => jc.1 + rem = d.2 ∧ jc.2 ≤ jc.1) ?_ ⟨Nat.zero_add _, le_rfl⟩
  intro rem jc t ⟨hsum, hc⟩
  dsimp only
  refine ⟨⟨hw, by omega, hc⟩, ?_⟩
  obtain ⟨h1, h2⟩ := clientResult_countDelStep (d.1, jc) t
  dsimp only at h1 h2
  exact ⟨by omega, by omega⟩

private theorem preservesAt_countDelProg (a : ℕ) (d : ℕ × ℕ) :
    PreservesAt a (countDelProg d) := by
  unfold countDelProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun jc => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold countDelStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  exact preservesAt_ite _ (preservesAt_pure _ _) (preservesAt_pure _ _)

private def commitStep (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := d.1
  let v := d.2
  let wv ← Memory.read (wBase n + v)
  let gv ← Memory.read (guessBase n + v)
  let xv ← Memory.read (sepOutBase n + v)
  let cv ← Memory.read (colBase n + v)
  let dout ← Memory.read (distBase n + (v + n + 2))
  if (wv = 1 ∧ gv = 0) ∨ xv = 1 then
    Memory.write (sepBase n + v) 1
  else
    Memory.write (sepBase n + v) 0
  if wv = 1 then
    if gv = 2 then Memory.write (colBase n + v) 1 else Memory.write (colBase n + v) 0
  else
    if dout < splitCount n then
      if cv = 1 then Memory.write (colBase n + v) 1 else Memory.write (colBase n + v) 0
    else
      if cv = 1 then Memory.write (colBase n + v) 0 else Memory.write (colBase n + v) 1
  pure (v + 1)

private theorem commitStep_realizes :
    Realizes .exact commitStep (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 < d.1) (fun _ _ => 0) := by
  unfold commitStep
  realize
  all_goals
    obtain ⟨hw, hv⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, wBase, guessBase, sepOutBase, parBase, distBase,
      flowBase, colBase, sepBase, splitCount] at *
    have hsq := splitCount_sq d.1
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_commitStep (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (commitStep d) = d.2 + 1 := by
  unfold commitStep
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
    clientResult_bind_read, clientResult_bind_read]
  dsimp only
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private def commitLeafProg (n : ℕ) : Memory.Prog Unit := do
  let _ ← Memory.read 0
  let _ ← iterate commitStep n n 0
  pure ()

private theorem commitLeafProg_realizes :
    Realizes .exact commitLeafProg (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w n _ => Fits w (octWorkspace n)) (fun _ _ => 0) := by
  unfold commitLeafProg
  realize [commitStep_realizes]
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (v : ℕ) _ => v + rem = d) ?_ (Nat.zero_add _)
  intro rem v t hsum
  dsimp only
  refine ⟨⟨h, by omega⟩, ?_⟩
  rw [clientResult_commitStep]
  omega

private theorem preservesAt_commitLeafProg {a n : ℕ}
    (ha : a < sepBase n ∨ wBase n ≤ a) :
    PreservesAt a (commitLeafProg n) := by
  unfold commitLeafProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_nat fun v hv => ⟨fun s => ?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold commitStep
    have hsep : a ≠ sepBase n + v := by dsimp only [sepBase, wBase] at ha ⊢; omega
    have hcol : a ≠ colBase n + v := by dsimp only [sepBase, colBase, wBase] at ha ⊢; omega
    rw [clientState_bind_read, clientState_bind_read, clientState_bind_read,
      clientState_bind_read, clientState_bind_read]
    dsimp only
    split_ifs <;>
      (rw [clientState_bind_write, clientState_bind_write, clientState_pure]
       dsimp only
       rw [Function.update_of_ne hcol, Function.update_of_ne hsep])
  · exact clientResult_commitStep (n, v) s

private def leafProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let k := d.1.1.2
  let m := d.1.2
  let L := d.2
  unpackGuessProg (n, L)
  let ok ← checkProperProg ((n, m), L)
  if ok = 1 then
    buildTerminalsProg ((n, m), L)
    let sepCnt ← minSepProg (n, m)
    let delCnt ← countDelProg (n, L)
    if sepCnt ≤ n ∧ delCnt ≤ n ∧ delCnt + sepCnt ≤ k then
      commitLeafProg n
      pure 1
    else
      pure 0
  else
    pure 0

private theorem leafProg_realizes :
    Realizes .exact leafProg (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 ≤ d.1.1.1)
      (fun _ _ => 0) := by
  unfold leafProg
  realize [unpackGuessProg_realizes, checkProperProg_realizes, buildTerminalsProg_realizes,
    minSepProg_realizes, countDelProg_realizes, commitLeafProg_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace] at *
    first | exact hw | omega | (apply hw.of_le; omega)

private theorem preservesAt_leafProg {a : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ}
    (ha : a < sepBase d.1.1.1 ∨ (wBase d.1.1.1 ≤ a ∧ a < guessBase d.1.1.1)) :
    PreservesAt a (leafProg d) := by
  have hg : a < guessBase d.1.1.1 := by
    dsimp only [sepBase, wBase, guessBase] at ha ⊢; omega
  have hk : a < keepBase d.1.1.1 := by
    dsimp only [guessBase, keepBase] at hg ⊢; omega
  have hf : a < flowBase d.1.1.1 := by
    dsimp only [keepBase, flowBase] at hk ⊢; omega
  have hc : a < sepBase d.1.1.1 ∨ wBase d.1.1.1 ≤ a := ha.imp id And.left
  unfold leafProg
  refine preservesAt_bind (preservesAt_unpackGuessProg hg) fun _ => ?_
  refine preservesAt_bind (preservesAt_checkProperProg a _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_buildTerminalsProg hk) fun _ => ?_
  refine preservesAt_bind (preservesAt_minSepProg hf) fun _ => ?_
  refine preservesAt_bind (preservesAt_countDelProg a _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind (preservesAt_commitLeafProg hc) fun _ => preservesAt_pure _ _

private def incOdomStep (d : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1
  let j := d.2.1
  let carry := d.2.2
  let dj ← Memory.read (digitBase n + j)
  if carry = 1 then
    if dj < 2 then
      Memory.write (digitBase n + j) (dj + 1)
      pure (j + 1, 0)
    else
      Memory.write (digitBase n + j) 0
      pure (j + 1, 1)
  else
    pure (j + 1, 0)

private theorem incOdomStep_realizes :
    Realizes .exact incOdomStep (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2.1 < d.1)
      (fun _ _ => 0) := by
  unfold incOdomStep
  realize
  all_goals
    obtain ⟨hw, hj⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase] at *
    first | omega | (apply hw.of_le; omega)

private theorem clientResult_incOdomStep_fst (d : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (incOdomStep d)).1 = d.2.1 + 1 := by
  unfold incOdomStep
  rw [clientResult_bind_read]
  split_ifs <;> simp only [clientResult_bind_write, clientResult_pure]

private def incOdomProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  let res ← iterate incOdomStep d.1 d.2 (0, 1)
  pure res.2

private theorem incOdomProg_realizes :
    Realizes .exact incOdomProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1) ∧ d.2 ≤ d.1) (fun _ _ => 0) := by
  unfold incOdomProg
  realize [incOdomStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace] at *
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (jc : ℕ × ℕ) _ => jc.1 + rem = d.2) ?_ (Nat.zero_add _)
  intro rem jc t hsum
  dsimp only
  refine ⟨⟨hw, by omega⟩, ?_⟩
  rw [clientResult_incOdomStep_fst]
  dsimp only
  omega

private def guessStep (d : (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let _ ← Memory.read 0
  let found' ← if d.2.2 = 0 then leafProg d.1 else pure d.2.2
  let done' ← incOdomProg (d.1.1.1.1, d.1.2)
  pure (done', found')

private theorem guessStep_realizes :
    Realizes .exact guessStep
      (WordEncoding.encode (α := (((ℕ × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1.1) ∧ d.1.2 ≤ d.1.1.1.1)
      (fun _ _ => 0) := by
  unfold guessStep
  realize [leafProg_realizes, incOdomProg_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    first | exact hw | exact hL

/-- Clamped base-3 evaluation of `L` digits starting at `base` in `mem`. -/
private def base3At (mem : ℕ → ℕ) (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => base3At mem base j + min (mem (base + j)) 2 * 3 ^ j

private theorem base3At_lt (mem : ℕ → ℕ) (base : ℕ) :
    ∀ L, base3At mem base L < 3 ^ L
  | 0 => by simp [base3At]
  | j + 1 => by
    have ih := base3At_lt mem base j
    have hmin : min (mem (base + j)) 2 ≤ 2 := Nat.min_le_right _ _
    have hmul : min (mem (base + j)) 2 * 3 ^ j ≤ 2 * 3 ^ j := Nat.mul_le_mul_right _ hmin
    simp only [base3At, pow_succ]
    omega

private theorem base3At_congr {m₁ m₂ : ℕ → ℕ} {base : ℕ} :
    ∀ {L}, (∀ i < L, m₁ (base + i) = m₂ (base + i)) → base3At m₁ base L = base3At m₂ base L
  | 0, _ => rfl
  | j + 1, h => by
    unfold base3At
    rw [base3At_congr fun i hi => h i (by omega), h j (by omega)]

private theorem incOdomProg_base3At (n L : ℕ) (s : Memory.State) :
    let done' := (Memory.spec 0).clientResult s (incOdomProg (n, L))
    let s' := (Memory.spec 0).clientState s (incOdomProg (n, L))
    done' ≤ 1 ∧
      base3At s'.mem (digitBase n) L + done' * 3 ^ L = base3At s.mem (digitBase n) L + 1 := by
  unfold incOdomProg
  simp only [client_simps]
  have hinv := iterate_invariant_of incOdomStep n
    (fun rem (jc : ℕ × ℕ) t =>
      jc.1 + rem = L ∧ jc.2 ≤ 1 ∧
        (∀ i, jc.1 ≤ i → t.mem (digitBase n + i) = s.mem (digitBase n + i)) ∧
        base3At t.mem (digitBase n) jc.1 + jc.2 * 3 ^ jc.1 =
          base3At s.mem (digitBase n) jc.1 + 1)
    (fun rem jc t ⟨hsum, hcarry, habove, hval⟩ => by
      dsimp only [incOdomStep]
      have hdj : t.mem (digitBase n + jc.1) = s.mem (digitBase n + jc.1) := habove jc.1 le_rfl
      by_cases hc : jc.2 = 1
      · by_cases hlt : t.mem (digitBase n + jc.1) < 2
        · rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hc, ite_eq_left hlt,
            clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          have hpre : base3At (Function.update t.mem (digitBase n + jc.1)
              (t.mem (digitBase n + jc.1) + 1)) (digitBase n) jc.1 =
              base3At t.mem (digitBase n) jc.1 :=
            base3At_congr fun i hi => Function.update_of_ne (by omega) _ _
          refine ⟨by omega, by omega,
            fun i hi => (Function.update_of_ne (by omega) _ _).trans (habove i (by omega)), ?_⟩
          simp only [base3At, hpre, Function.update_self, zero_mul, add_zero]
          rw [hc, one_mul] at hval
          have hmin1 : min (t.mem (digitBase n + jc.1) + 1) 2 = t.mem (digitBase n + jc.1) + 1 :=
            Nat.min_eq_left (by omega)
          have hmin0 : min (s.mem (digitBase n + jc.1)) 2 = t.mem (digitBase n + jc.1) := by
            rw [← hdj]; exact Nat.min_eq_left (by omega)
          rw [hmin1, hmin0, add_mul, one_mul]
          omega
        · rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hc, ite_eq_right hlt,
            clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
          dsimp only
          have hpre : base3At (Function.update t.mem (digitBase n + jc.1) 0)
              (digitBase n) jc.1 = base3At t.mem (digitBase n) jc.1 :=
            base3At_congr fun i hi => Function.update_of_ne (by omega) _ _
          refine ⟨by omega, by omega,
            fun i hi => (Function.update_of_ne (by omega) _ _).trans (habove i (by omega)), ?_⟩
          simp only [base3At, hpre, Function.update_self, Nat.zero_min, zero_mul, add_zero,
            one_mul, pow_succ]
          rw [hc, one_mul] at hval
          have hmin0 : min (s.mem (digitBase n + jc.1)) 2 = 2 := by
            rw [← hdj]; exact Nat.min_eq_right (by omega)
          rw [hmin0]
          omega
      · have hc0 : jc.2 = 0 := by omega
        rw [clientResult_bind_read, clientState_bind_read, ite_eq_right hc,
          clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, by omega, fun i hi => habove i (by omega), ?_⟩
        simp only [base3At, hdj, zero_mul, add_zero]
        rw [hc0, zero_mul, add_zero] at hval
        omega)
    (n := L) (a := (0, 1)) (s := s) ⟨Nat.zero_add _, le_rfl, fun _ _ => rfl, by simp [base3At]⟩
  obtain ⟨hL0, hcarry, _, hval⟩ := hinv
  have hfst : ((Memory.spec 0).clientResult s (iterate incOdomStep n L (0, 1))).1 = L := by omega
  rw [hfst] at hval
  exact ⟨hcarry, hval⟩

private def compressProg (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let n := d.1.1.1
  let L := d.2
  fillRange ((digitBase n, 0), L)
  let res ← boundedWhile (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep d (3 ^ L) (0, 0)
  pure res.2

private theorem compressProg_realizes :
    Realizes .exact compressProg (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1.1) ∧ d.2 ≤ d.1.1.1)
      (fun _ _ => 0) := by
  unfold compressProg
  realize [fillRange_realizes, guessStep_realizes]
  all_goals
    obtain ⟨hw, hL⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, digitBase] at *
    try omega
    try (apply hw.of_le; omega)
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun (_ : ℕ × ℕ) _ => True)
    (fun (st : ℕ × ℕ) t => if st.1 = 0 then 3 ^ d.2 - base3At t.mem (digitBase d.1.1.1) d.2 else 0)
    ?_ ?_ trivial ?_ hv
  · intro st t _ hzero hg
    have hlt := base3At_lt t.mem (digitBase d.1.1.1) d.2
    simp only [hg, ↓reduceIte] at hzero
    omega
  · intro st t _ hg _
    refine ⟨⟨hw, hL⟩, trivial, ?_⟩
    have hlt := base3At_lt t.mem (digitBase d.1.1.1) d.2
    by_cases h0 : st.2 = 0
    · have hres : ((Memory.spec 0).clientResult t (guessStep (d, st))).1 =
          (Memory.spec 0).clientResult ((Memory.spec 0).clientState t (leafProg d))
            (incOdomProg (d.1.1.1, d.2)) := by
        unfold guessStep
        rw [clientResult_bind_read, ite_eq_left h0, clientResult_bind, clientResult_bind,
          clientResult_pure]
      have hst : (Memory.spec 0).clientState t (guessStep (d, st)) =
          (Memory.spec 0).clientState ((Memory.spec 0).clientState t (leafProg d))
            (incOdomProg (d.1.1.1, d.2)) := by
        unfold guessStep
        rw [clientState_bind_read, ite_eq_left h0, clientState_bind, clientState_bind,
          clientState_pure]
      simp only [hres, hst, hg, ↓reduceIte]
      have hpres : base3At ((Memory.spec 0).clientState t (leafProg d)).mem
          (digitBase d.1.1.1) d.2 = base3At t.mem (digitBase d.1.1.1) d.2 := by
        refine base3At_congr fun i hi => preservesAt_leafProg (Or.inr ⟨?_, ?_⟩) t
        · dsimp only [wBase, digitBase]; omega
        · dsimp only [digitBase, guessBase]; omega
      have hodom := incOdomProg_base3At d.1.1.1 d.2 ((Memory.spec 0).clientState t (leafProg d))
      dsimp only at hodom
      obtain ⟨hdone_le, hodom_eq⟩ := hodom
      rw [hpres] at hodom_eq
      split_ifs with hdone0
      · rw [hdone0, zero_mul, add_zero] at hodom_eq; omega
      · omega
    · have hres : ((Memory.spec 0).clientResult t (guessStep (d, st))).1 =
          (Memory.spec 0).clientResult t (incOdomProg (d.1.1.1, d.2)) := by
        unfold guessStep
        rw [clientResult_bind_read, ite_eq_right h0, clientResult_bind, clientState_pure,
          clientResult_bind, clientResult_pure]
      have hst : (Memory.spec 0).clientState t (guessStep (d, st)) =
          (Memory.spec 0).clientState t (incOdomProg (d.1.1.1, d.2)) := by
        unfold guessStep
        rw [clientState_bind_read, ite_eq_right h0, clientState_bind, clientState_pure,
          clientState_bind, clientState_pure]
      simp only [hres, hst, hg, ↓reduceIte]
      have hodom := incOdomProg_base3At d.1.1.1 d.2 t
      dsimp only at hodom
      obtain ⟨hdone_le, hodom_eq⟩ := hodom
      split_ifs with hdone0
      · rw [hdone0, zero_mul, add_zero] at hodom_eq; omega
      · omega
  · simp only [↓reduceIte]
    exact Nat.sub_le _ _

private def octStep (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let n := d.1.1
  let k := d.1.2
  let m := d.2.1
  let alive := d.2.2
  let _ ← Memory.read 0
  if alive = 1 then
    let L ← buildWProg (n, m)
    if L ≤ k then
      Memory.write (sepBase n + m) 1
      pure (m + 1, 1)
    else if L ≤ n then
      let ok ← compressProg (((n, k), m + 1), L)
      pure (m + 1, ok)
    else
      pure (m + 1, 0)
  else
    pure (m + 1, 0)

private theorem octStep_realizes :
    Realizes .exact octStep (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d _ => Fits w (octWorkspace d.1.1) ∧ d.2.1 < d.1.1)
      (fun _ _ => 0) := by
  unfold octStep
  realize [buildWProg_realizes, compressProg_realizes]
  all_goals
    obtain ⟨hw, hm⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, sepBase] at *
    first | exact hw | omega | (apply hw.of_le; omega)

private theorem clientResult_octStep_fst (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientResult s (octStep d)).1 = d.2.1 + 1 := by
  unfold octStep
  rw [clientResult_bind_read]
  split_ifs <;> try rfl
  rw [clientResult_bind]
  split_ifs <;> simp only [clientResult_bind, clientResult_pure]

private def octProg (_ : Unit) : Memory.Prog ℕ := do
  let n ← Memory.read 1
  let k ← Memory.read 2
  let _ ← Memory.alloc (octScratch n)
  fillRange ((sepBase n, 0), n)
  fillRange ((colBase n, 0), n)
  let res ← iterate octStep (n, k) n (0, 1)
  pure res.2

private theorem octProg_realizes :
    Realizes .exact octProg (WordEncoding.encode (α := Unit))
      (WordEncoding.encode (α := ℕ))
      (fun w _ s => s.frontier = 3 + s.mem 1 * s.mem 1 ∧ Fits w (octWorkspace (s.mem 1)))
      (fun _ _ => 0) := by
  unfold octProg
  realize [fillRange_realizes, octStep_realizes]
  all_goals
    obtain ⟨hfr, hw⟩ := h
    dsimp -failIfUnchanged only [octWorkspace, octScratch, sepBase, colBase, splitCount] at *
    have hsq := splitCount_sq (s.mem 1)
    try omega
    try (apply hw.of_le; omega)
  refine iterationSafe_of_stepInv _ _ w _
    (fun rem (ma : ℕ × ℕ) _ => ma.1 + rem = s.mem 1) ?_ (Nat.zero_add _)
  intro rem ma t hsum
  dsimp only
  refine ⟨⟨hw, by omega⟩, ?_⟩
  rw [clientResult_octStep_fst]
  dsimp only
  omega

/-! ### Admissibility (`ValidHistory`) and `memoryCost` bounds -/

private abbrev MemReady (w n : ℕ) (s : Memory.State) : Prop :=
  Memory.WellFormed w s ∧ octWorkspace n ≤ s.frontier

private theorem validHistory_bind_ready {α β : Type} {w n : ℕ} {s : Memory.State}
    (hs : MemReady w n s) {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ x t, MemReady w n t →
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (q x))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_step hp (hq _ _ (MonotoneMemInv.pres hs hp))

private theorem mc_pure {α : Type} (x : α) (s : Memory.State) :
    memoryCost (pure x) s ≤ 0 := le_refl 0

private theorem mc_read (a : ℕ) (s : Memory.State) :
    memoryCost (Memory.read a) s ≤ 1 := le_refl 1

private theorem mc_write (a v : ℕ) (s : Memory.State) :
    memoryCost (Memory.write a v) s ≤ 1 := le_refl 1

private theorem memReady_write {w n : ℕ} {s : Memory.State} (hs : MemReady w n s) (a v : ℕ)
    (hv : Fits w v) : MemReady w n ⟨Function.update s.mem a v, s.frontier⟩ := by
  refine ⟨⟨hs.1.frontier_fits, fun b => ?_⟩, hs.2⟩
  dsimp only
  by_cases hb : b = a
  · subst hb; simpa using hv
  · rw [Function.update_of_ne hb]; exact hs.1.mem_fits b

private theorem memoryCost_boundedWhile_le_of {δ σ : Type}
    (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
    (body : δ × σ → Memory.Prog σ) (c : ℕ) (d : δ)
    (hstep : ∀ a s, guard d a → memoryCost (body (d, a)) s ≤ c)
    (m : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (boundedWhile guard body d m a) s ≤ c * m := by
  induction m generalizing a s with
  | zero => simp [boundedWhile]
  | succ m ih =>
    unfold boundedWhile
    by_cases hg : guard d a
    · rw [ite_eq_left hg, memoryCost_bind']
      have h1 := hstep a s hg
      have h2 := ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))
      rw [Nat.mul_succ]
      omega
    · rw [ite_eq_right hg]
      simp

private theorem validHistory_fillRange {w n : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w n s) (hend : d.1.1 + d.2 ≤ octWorkspace n) (hval : Fits w d.1.2) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillRange d)) := by
  rcases d with ⟨⟨base, val⟩, len⟩
  unfold fillRange
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) len 0 (fun idx hidx t ht => ⟨?_, ?_⟩) hs)
    (validHistory_pure _ _ _)
  · unfold fillStep
    dsimp only at hend ⊢
    exact validHistory_write_bind (by have := ht.2; omega) hval (validHistory_pure _ _ _)
  · unfold fillStep; simp only [client_simps]

private theorem validHistory_copyRange {w n : ℕ} {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w n s) (hsrc : d.1.1 + d.2 ≤ octWorkspace n)
    (hdst : d.1.2 + d.2 ≤ octWorkspace n) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyRange d)) := by
  rcases d with ⟨⟨srcB, dstB⟩, len⟩
  unfold copyRange
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) len 0 (fun idx hidx t ht => ⟨?_, ?_⟩) hs)
    (validHistory_pure _ _ _)
  · unfold copyStep
    dsimp only at hsrc hdst ⊢
    exact validHistory_read_bind (by have := ht.2; omega)
      (validHistory_write_bind (by have := ht.2; omega) (ht.1.mem_fits _)
        (validHistory_pure _ _ _))
  · unfold copyStep; simp only [client_simps]

private theorem validHistory_readSplitCap {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readSplitCap d)) := by
  rcases d with ⟨⟨⟨n, m⟩, x⟩, y⟩
  have hfr := hs.2
  dsimp only [octWorkspace] at hfr
  unfold readSplitCap
  dsimp only
  refine validHistory_read_bind (by omega) ?_
  split_ifs
  all_goals
    first
    | exact validHistory_pure _ _ _
    | (refine validHistory_read_bind ?_ ?_
       · dsimp only [splitCount, keepBase, flipBase, wBase] at *
         first
         | omega
         | (have hu : x - (n + 2) < n := by omega
            have hmul : (x - (n + 2)) * n < n * n := Nat.mul_lt_mul_of_pos_right hu (by omega)
            omega)
       · exact validHistory_ite (fun _ => validHistory_pure _ _ _)
           (fun _ => validHistory_pure _ _ _))

private theorem validHistory_readResCap {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hs : MemReady w d.1.1.1 s) (hx : d.1.2 < splitCount d.1.1.1) (hy : d.2 < splitCount d.1.1.1) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readResCap d)) := by
  rcases d with ⟨⟨⟨n, m⟩, x⟩, y⟩
  dsimp only at hs hx hy
  unfold readResCap
  refine validHistory_bind_step (validHistory_readSplitCap hs) ?_
  rw [clientState_readSplitCap]
  dsimp only
  have hfr := hs.2
  have hsq := splitCount_sq n
  have h1 : flowBase n + x * splitCount n + y < s.frontier := by
    have hlt : x * splitCount n + y < splitCount n * splitCount n := by nlinarith
    dsimp only [octWorkspace, flowBase, splitCount] at hfr hlt ⊢
    omega
  have h2 : flowBase n + y * splitCount n + x < s.frontier := by
    have hlt : y * splitCount n + x < splitCount n * splitCount n := by nlinarith
    dsimp only [octWorkspace, flowBase, splitCount] at hfr hlt ⊢
    omega
  exact validHistory_read_bind h1 (validHistory_read_bind h2
    (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)))

private theorem validHistory_bfsProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bfsProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hs
  have hsq := splitCount_sq n
  unfold bfsProg
  dsimp only
  have hfill : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fillRange ((distBase n, splitCount n), splitCount n))) :=
    validHistory_fillRange hs
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount]; omega)
      (by apply hw.of_le; dsimp only [octWorkspace, splitCount]; omega)
  refine validHistory_bind_step hfill ?_
  have hs1 := MonotoneMemInv.pres hs hfill
  refine validHistory_write_bind
    (by have := hs1.2; dsimp only [octWorkspace, distBase, flowBase, splitCount] at *; omega)
    (fits_zero w) ?_
  refine validHistory_write_bind
    (by have := hs1.2; dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at *;
        omega)
    (fits_zero w) ?_
  have hs2 := memReady_write (memReady_write hs1 (distBase n) 0 (fits_zero w))
    (parBase n) 0 (fits_zero w)
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n - 1) 0
      (fun layer hlayer t ht => ⟨?_, ?_⟩) hs2)
    (validHistory_pure _ _ _)
  · unfold bfsLayerStep
    dsimp only
    refine validHistory_read_bind
      (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n) 0
        (fun u hu t' ht' => ⟨?_, ?_⟩) ht)
      (validHistory_pure _ _ _)
    · unfold bfsMidStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht'.2
            dsimp only [octWorkspace, distBase, flowBase, splitCount] at hu this ⊢; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := MemReady w n) (splitCount n) 0
          (fun v hv t'' ht'' => ⟨?_, ?_⟩) ht')
        (validHistory_pure _ _ _)
      · unfold bfsInnerStep
        dsimp only
        have hdv : distBase n + v < t''.frontier := by
          have := ht''.2
          dsimp only [octWorkspace, distBase, flowBase, splitCount] at hv this ⊢; omega
        refine validHistory_read_bind hdv ?_
        have hrc := validHistory_readResCap (d := (((n, m), u), v)) ht''
          (by dsimp only; omega) (by dsimp only; omega)
        refine validHistory_bind_step hrc ?_
        have ht3 := MonotoneMemInv.pres ht'' hrc
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_write_bind
          (by have := ht3.2
              dsimp only [octWorkspace, distBase, flowBase, splitCount] at hv this ⊢; omega)
          (by apply hw.of_le; dsimp only [octWorkspace, splitCount] at hlayer ⊢; omega) ?_
        exact validHistory_write_bind
          (by have := ht3.2
              dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hv this ⊢
              omega)
          (by apply hw.of_le; dsimp only [octWorkspace, splitCount] at hu ⊢; omega)
          (validHistory_pure _ _ _)
      · exact clientResult_bfsInnerStep _ t''
    · exact clientResult_bfsMidStep _ t'
  · unfold bfsLayerStep; simp only [client_simps]

private theorem validHistory_minSepProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minSepProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hs
  have hsq := splitCount_sq n
  unfold minSepProg
  dsimp only
  have hfill := validHistory_fillRange (d := ((flowBase n, 0), splitCount n * splitCount n))
    hs (by dsimp only [octWorkspace, flowBase, splitCount]; omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  have hs1 := MonotoneMemInv.pres hs hfill
  have haug := validHistory_iterate_inv (MemReady w n) augRoundStep (n, m)
    (fun r t ht => by
      unfold augRoundStep
      dsimp only
      have hbfs := validHistory_bfsProg (d := (n, m)) hw ht
      refine validHistory_bind_step hbfs ?_
      have ht1 := MonotoneMemInv.pres ht hbfs
      refine validHistory_read_bind
        (by have := ht1.2
            dsimp only [octWorkspace, distBase, flowBase, splitCount] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_inv (MemReady w n) pushUnitStep n (fun cur t' ht' => ?_) _ 1 ht1)
        (validHistory_pure _ _ _)
      unfold pushUnitStep
      dsimp only
      refine validHistory_read_bind (by have := ht'.2; dsimp only [octWorkspace] at *; omega) ?_
      refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_read_bind
        (by have := ht'.2
            dsimp only [octWorkspace, parBase, distBase, flowBase, splitCount] at hcur this ⊢
            omega)
        ?_
      refine validHistory_ite (fun hu => ?_) (fun _ => validHistory_pure _ _ _)
      have had1 : flowBase n + cur * splitCount n +
          t'.mem (parBase n + cur) < t'.frontier := by
        have hlt : cur * splitCount n + t'.mem (parBase n + cur) <
            splitCount n * splitCount n := by nlinarith
        have := ht'.2
        dsimp only [octWorkspace, flowBase, splitCount] at hlt this ⊢; omega
      have had2 : flowBase n + t'.mem (parBase n + cur) * splitCount n +
          cur < t'.frontier := by
        have hlt : t'.mem (parBase n + cur) * splitCount n + cur <
            splitCount n * splitCount n := by nlinarith
        have := ht'.2
        dsimp only [octWorkspace, flowBase, splitCount] at hlt this ⊢; omega
      refine validHistory_read_bind had1 ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
      · exact validHistory_write_bind had1 ((ht'.1.mem_fits _).of_le (Nat.sub_le _ _))
          (validHistory_pure _ _ _)
      · refine validHistory_read_bind had2 ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_write_bind had2
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
    n 0 hs1
  refine validHistory_bind_step haug ?_
  have hs2 := MonotoneMemInv.pres hs1 haug
  have hbfs2 := validHistory_bfsProg (d := (n, m)) hw hs2
  refine validHistory_bind_step hbfs2 ?_
  have hs3 := MonotoneMemInv.pres hs2 hbfs2
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := MemReady w n) n 0 0
      (fun v hv cnt t ht => ⟨?_, ?_⟩) hs3)
    (validHistory_pure _ _ _)
  · unfold extractSepStep
    dsimp only
    have hfr := ht.2
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, wBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    have hsep : sepOutBase n + v < t.frontier := by
      dsimp only [octWorkspace, sepOutBase, parBase, distBase, flowBase, splitCount] at hfr hv ⊢
      omega
    exact validHistory_ite
      (fun _ => validHistory_write_bind hsep
        (by apply hw.of_le; dsimp only [octWorkspace]; omega) (validHistory_pure _ _ _))
      (fun _ => validHistory_write_bind hsep (fits_zero w) (validHistory_pure _ _ _))
  · exact (clientResult_extractSepStep _ t).1

private theorem validHistory_buildWProg {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1)) (hm : d.2 < d.1) (hs : MemReady w d.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildWProg d)) := by
  rcases d with ⟨n, m⟩
  dsimp only at hw hm hs
  unfold buildWProg
  dsimp only
  have hcp := validHistory_copyRange (d := ((sepBase n, wBase n), n)) hs
    (by dsimp only [octWorkspace, sepBase]; omega)
    (by dsimp only [octWorkspace, wBase]; omega)
  refine validHistory_bind_step hcp ?_
  have hs1 := MonotoneMemInv.pres hs hcp
  have hwm : wBase n + m <
      ((Memory.spec 0).clientState s (copyRange ((sepBase n, wBase n), n))).frontier := by
    have := hs1.2; dsimp only [octWorkspace, wBase] at *; omega
  have h1 : Fits w 1 := by apply hw.of_le; dsimp only [octWorkspace]; omega
  refine validHistory_write_bind hwm h1 ?_
  have hs2 := memReady_write hs1 (wBase n + m) 1 h1
  have hloop : ∀ rem vL t, vL.1 + rem = n → vL.2 ≤ vL.1 → MemReady w n t →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate buildWListStep n rem vL)) := by
    intro rem
    induction rem with
    | zero => intro vL t _ _ _; exact validHistory_pure _ _ _
    | succ rem ih =>
      intro vL t hsum hL ht
      have hvstep : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (buildWListStep (n, vL))) := by
        unfold buildWListStep
        dsimp only
        refine validHistory_read_bind
          (by have := ht.2; dsimp only [octWorkspace, wBase] at *; omega) ?_
        exact validHistory_ite
          (fun _ => validHistory_write_bind
            (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega)
            (by apply hw.of_le; dsimp only [octWorkspace]; omega)
            (validHistory_pure _ _ _))
          (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step hvstep ?_
      have ht' := MonotoneMemInv.pres ht hvstep
      refine ih _ _ ?_ ?_ ht'
      · obtain ⟨h1, _⟩ := clientResult_buildWListStep (n, vL) t; dsimp only at h1; omega
      · obtain ⟨h1, h2⟩ := clientResult_buildWListStep (n, vL) t; dsimp only at h1 h2; omega
  exact validHistory_bind_step (hloop n (0, 0) _ (Nat.zero_add _) le_rfl hs2)
    (validHistory_pure _ _ _)

private theorem validHistory_leafProg {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1.1.1)) (hL : d.2 ≤ d.1.1.1) (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (leafProg d)) := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hw hL hs
  have h1 : Fits w 1 := by apply hw.of_le; dsimp only [octWorkspace]; omega
  unfold leafProg
  dsimp only
  have hunpack : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (unpackGuessProg (n, L))) := by
    unfold unpackGuessProg
    dsimp only
    have hf := validHistory_fillRange (d := ((guessBase n, 0), n)) hs
      (by dsimp only [octWorkspace, guessBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) L 0 (fun j hj t ht => ⟨?_, ?_⟩)
        (MonotoneMemInv.pres hs hf))
      (validHistory_pure _ _ _)
    · unfold unpackStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      exact validHistory_ite
        (fun hcond => validHistory_write_bind
          (by have := ht.2; dsimp only [octWorkspace, guessBase] at *; omega)
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_pure _ _ _)
    · exact clientResult_unpackStep _ t
  refine validHistory_bind_ready hs hunpack fun _ t1 hs1 => ?_
  refine validHistory_bind_ready hs1 ?_ fun _ t2 hs2 => ?_
  · unfold checkProperProg
    dsimp only
    refine validHistory_read_bind (by have := hs1.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 1 (fun i hi ok t ht => ⟨?_, ?_⟩) hs1)
      (validHistory_pure _ _ _)
    · unfold properOuterStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_fst (Inv := MemReady w n) L 0 ok (fun j hj ok' t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold properInnerStep
        dsimp only
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
        refine validHistory_ite (fun hcond => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_read_bind ?_
          (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
        have := ht'.2
        have hmul : t.mem (wListBase n + i) * n < n * n :=
          Nat.mul_lt_mul_of_pos_right hcond.1 (by omega)
        dsimp only [octWorkspace] at this ⊢; omega
      · exact clientResult_properInnerStep_fst _ t'
    · exact clientResult_properOuterStep_fst _ t
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_ready hs2 ?_ fun _ t3 hs3 => ?_
  · unfold buildTerminalsProg
    dsimp only
    have hf1 := validHistory_fillRange (d := ((keepBase n, 0), n)) hs2
      (by dsimp only [octWorkspace, keepBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf1 ?_
    have hs2a := MonotoneMemInv.pres hs2 hf1
    have hf2 := validHistory_fillRange (d := ((flipBase n, 0), n)) hs2a
      (by dsimp only [octWorkspace, flipBase]; omega) (fits_zero w)
    refine validHistory_bind_step hf2 ?_
    have hs2b := MonotoneMemInv.pres hs2a hf2
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := MemReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs2b)
      (validHistory_pure _ _ _)
    · unfold termOuterStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, wBase] at *; omega) ?_
      refine validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, colBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := MemReady w n) L 0 (fun j hj t' ht' => ⟨?_, ?_⟩) ht)
        (validHistory_pure _ _ _)
      · unfold termInnerStep
        dsimp only
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, wListBase] at *; omega) ?_
        refine validHistory_read_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
        refine validHistory_ite (fun hcond => ?_) (fun _ => validHistory_pure _ _ _)
        have hadj : 3 + t'.mem (wListBase n + j) * n + v < t'.frontier := by
          have := ht'.2
          have hmul : t'.mem (wListBase n + j) * n < n * n :=
            Nat.mul_lt_mul_of_pos_right hcond.1 (by omega)
          dsimp only [octWorkspace] at this ⊢; omega
        refine validHistory_read_bind hadj ?_
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        exact validHistory_ite
          (fun _ => validHistory_write_bind
            (by have := ht'.2; dsimp only [octWorkspace, flipBase] at *; omega) h1
            (validHistory_pure _ _ _))
          (fun _ => validHistory_write_bind
            (by have := ht'.2; dsimp only [octWorkspace, keepBase] at *; omega) h1
            (validHistory_pure _ _ _))
      · exact clientResult_termInnerStep _ t'
    · exact clientResult_termOuterStep _ t
  refine validHistory_bind_ready hs3 (validHistory_minSepProg (d := (n, m)) hw hs3)
    fun _ t4 hs4 => ?_
  refine validHistory_bind_ready hs4 ?_ fun _ t5 hs5 => ?_
  · unfold countDelProg
    dsimp only
    refine validHistory_read_bind (by have := hs4.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 0 (fun j hj cnt t ht => ⟨?_, ?_⟩) hs4)
      (validHistory_pure _ _ _)
    · unfold countDelStep
      dsimp only
      exact validHistory_read_bind
        (by have := ht.2; dsimp only [octWorkspace, digitBase] at *; omega)
        (validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _))
    · exact (clientResult_countDelStep _ t).1
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_ready hs5 ?_ fun _ _ _ => validHistory_pure _ _ _
  unfold commitLeafProg
  refine validHistory_read_bind (by have := hs5.2; dsimp only [octWorkspace] at *; omega) ?_
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := MemReady w n) n 0 (fun v hv t ht => ⟨?_, ?_⟩) hs5)
    (validHistory_pure _ _ _)
  · unfold commitStep
    dsimp only
    have hfr := ht.2
    have hsq := splitCount_sq n
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, wBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, guessBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, sepOutBase, parBase, distBase, flowBase,
        splitCount] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, colBase] at hfr hv ⊢; omega) ?_
    refine validHistory_read_bind
      (by dsimp only [octWorkspace, distBase, flowBase, splitCount] at hfr hv ⊢; omega) ?_
    have hsaddr : sepBase n + v < t.frontier := by
      dsimp only [octWorkspace, sepBase] at hfr hv ⊢; omega
    have hw1 : ∀ val, Fits w val →
        (Memory.spec w).ValidHistory ⟨Function.update t.mem (sepBase n + v) val, t.frontier⟩
          ((Memory.spec w).clientHistory ⟨Function.update t.mem (sepBase n + v) val, t.frontier⟩
            (do
              if t.mem (wBase n + v) = 1 then
                if t.mem (guessBase n + v) = 2 then Memory.write (colBase n + v) 1
                else Memory.write (colBase n + v) 0
              else if t.mem (distBase n + (v + n + 2)) < splitCount n then
                if t.mem (colBase n + v) = 1 then Memory.write (colBase n + v) 1
                else Memory.write (colBase n + v) 0
              else if t.mem (colBase n + v) = 1 then Memory.write (colBase n + v) 0
              else Memory.write (colBase n + v) 1
              pure (v + 1))) := by
      intro val _
      have hcaddr : colBase n + v < t.frontier := by
        dsimp only [octWorkspace, colBase] at hfr hv ⊢; omega
      split_ifs <;>
        first
        | exact validHistory_write_bind hcaddr h1 (validHistory_pure _ _ _)
        | exact validHistory_write_bind hcaddr (fits_zero w) (validHistory_pure _ _ _)
    exact validHistory_ite
      (fun _ => validHistory_write_bind hsaddr h1 (hw1 1 h1))
      (fun _ => validHistory_write_bind hsaddr (fits_zero w) (hw1 0 (fits_zero w)))
  · exact clientResult_commitStep _ t

private theorem validHistory_compressProg {w : ℕ} {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hw : Fits w (octWorkspace d.1.1.1)) (hL : d.2 ≤ d.1.1.1) (hs : MemReady w d.1.1.1 s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (compressProg d)) := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hw hL hs
  unfold compressProg
  dsimp only
  have hf := validHistory_fillRange (d := ((digitBase n, 0), L)) hs
    (by dsimp only [octWorkspace, digitBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf ?_
  have hs1 := MonotoneMemInv.pres hs hf
  refine validHistory_bind_step
    (validHistory_boundedWhile_inv (MemReady w n) (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep
      (((n, k), m), L) (fun st t ht _ => ?_) (3 ^ L) (0, 0) hs1)
    (validHistory_pure _ _ _)
  have hodom : ∀ (found' : ℕ) (t1 : Memory.State), MemReady w n t1 →
      (Memory.spec w).ValidHistory t1
        ((Memory.spec w).clientHistory t1
          (incOdomProg (n, L) >>= fun done' => pure (done', found'))) := by
    intro found' t1 ht1
    refine validHistory_bind_step ?_ (validHistory_pure _ _ _)
    unfold incOdomProg
    dsimp only
    refine validHistory_read_bind (by have := ht1.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_fst (Inv := MemReady w n) L 0 1
        (fun j hj carry t' ht' => ⟨?_, ?_⟩) ht1)
      (validHistory_pure _ _ _)
    · unfold incOdomStep
      dsimp only
      refine validHistory_read_bind
        (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      exact validHistory_ite
        (fun hlt => validHistory_write_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega)
          (by apply hw.of_le; dsimp only [octWorkspace]; omega)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_write_bind
          (by have := ht'.2; dsimp only [octWorkspace, digitBase] at *; omega)
          (fits_zero w) (validHistory_pure _ _ _))
    · exact clientResult_incOdomStep_fst _ t'
  dsimp only [guessStep]
  refine validHistory_read_bind (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · have hlf := validHistory_leafProg (d := (((n, k), m), L)) hw hL ht
    exact validHistory_bind_step hlf (hodom _ _ (MonotoneMemInv.pres ht hlf))
  · exact validHistory_bind_step (validHistory_pure _ _ _) (hodom _ t ht)

private theorem inputFits_encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    InputFits w (encodeInput G k) := by
  refine ⟨?_, ?_⟩
  · rw [length_encodeInput]
    apply hw.of_le
    dsimp only [octWorkspace]
    omega
  · intro u hu
    simp only [encodeInput, List.mem_cons] at hu
    rcases hu with rfl | rfl | hu
    · apply hw.of_le; dsimp only [octWorkspace]; omega
    · exact hk
    · simp only [encodeAdjMatrix, List.mem_ofFn] at hu
      obtain ⟨idx, rfl⟩ := hu
      split_ifs
      · apply hw.of_le; dsimp only [octWorkspace]; omega
      · exact fits_zero w

private theorem init_mem_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).mem 1 = n :=
  rfl

private theorem init_mem_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).mem 2 = k :=
  rfl

private theorem init_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (Memory.State.init (encodeInput G k)).frontier = 3 + n * n := by
  change (encodeInput G k).length + 1 = 3 + n * n
  rw [length_encodeInput]
  omega

private theorem validHistory_octProg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k w : ℕ} (hw : Fits w (octWorkspace n)) (hk : Fits w k) :
    let s₀ := Memory.State.init (encodeInput G k)
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (octProg ())) := by
  intro s₀
  have hfr0 : s₀.frontier = 3 + n * n := init_frontier G k
  have hm1 : s₀.mem 1 = n := init_mem_one G k
  have hm2 : s₀.mem 2 = k := init_mem_two G k
  have hin : InputFits w (encodeInput G k) := inputFits_encodeInput G hw hk
  have hfit0 : Fits w ((encodeInput G k).length + 1) := by
    rw [length_encodeInput]
    apply hw.of_le
    dsimp only [octWorkspace]
    omega
  have hwf0 : Memory.WellFormed w s₀ := Memory.wellFormed_init hin hfit0
  unfold octProg
  refine validHistory_read_bind (by omega) ?_
  rw [hm1]
  refine validHistory_read_bind (by omega) ?_
  rw [hm2]
  have halloc : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.alloc (octScratch n))) :=
    validHistory_alloc (by rw [hfr0, frontier_add_octScratch]; exact hw)
  refine validHistory_bind_step halloc ?_
  have hs1 : MemReady w n ((Memory.spec 0).clientState s₀ (Memory.alloc (octScratch n))) := by
    refine ⟨wellFormed_clientState hwf0 halloc, ?_⟩
    change octWorkspace n ≤ s₀.frontier + octScratch n
    rw [hfr0, frontier_add_octScratch]
  have hf1 := validHistory_fillRange (d := ((sepBase n, 0), n)) hs1
    (by dsimp only [octWorkspace, sepBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf1 ?_
  have hs2 := MonotoneMemInv.pres hs1 hf1
  have hf2 := validHistory_fillRange (d := ((colBase n, 0), n)) hs2
    (by dsimp only [octWorkspace, colBase]; omega) (fits_zero w)
  refine validHistory_bind_step hf2 ?_
  have hs3 := MonotoneMemInv.pres hs2 hf2
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := MemReady w n) n 0 1 (fun m hm alive t ht => ⟨?_, ?_⟩) hs3)
    (validHistory_pure _ _ _)
  · unfold octStep
    dsimp only
    refine validHistory_read_bind (by have := ht.2; dsimp only [octWorkspace] at *; omega) ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
    have hbw := validHistory_buildWProg (d := (n, m)) hw (by dsimp only; omega) ht
    refine validHistory_bind_step hbw ?_
    have ht1 := MonotoneMemInv.pres ht hbw
    refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
    · exact validHistory_write_bind
        (by have := ht1.2; dsimp only [octWorkspace, sepBase] at *; omega)
        (by apply hw.of_le; dsimp only [octWorkspace]; omega)
        (validHistory_pure _ _ _)
    · exact validHistory_ite
        (fun hLn => validHistory_bind_step
          (validHistory_compressProg (d := (((n, k), m + 1), _)) hw hLn ht1)
          (validHistory_pure _ _ _))
        (fun _ => validHistory_pure _ _ _)
  · exact clientResult_octStep_fst _ t

private theorem memoryCost_fillRange_le (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (fillRange d) s ≤ d.2 := by
  unfold fillRange
  have hit := memoryCost_iterate_le_of fillStep 1 d.1
    (fun idx t => by unfold fillStep; exact (le_refl 1)) d.2 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => mc_pure () t) (by omega)

private theorem memoryCost_copyRange_le (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (copyRange d) s ≤ 2 * d.2 := by
  unfold copyRange
  have hit := memoryCost_iterate_le_of copyStep 2 d.1
    (fun idx t => by
      unfold copyStep
      exact memoryCost_bind_le (mc_read _ t) fun _ t' => (le_refl 1 : memoryCost _ t' ≤ 1)) d.2 0 s
  exact le_trans (memoryCost_bind_le hit fun _ t => mc_pure () t) (by omega)

private theorem memoryCost_readSplitCap_le (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readSplitCap d) s ≤ 2 := by
  unfold readSplitCap
  have hbody : ∀ t, memoryCost
      (if d.1.2 = 0 then
        if 2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
          do let a ← Memory.read (keepBase d.1.1.1 + (d.2 - 2))
             if a = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else if d.2 = 1 then
        if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 then
          do let b ← Memory.read (flipBase d.1.1.1 + (d.1.2 - (d.1.1.1 + 2)))
             if b = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else if 2 ≤ d.1.2 ∧ d.1.2 < d.1.1.1 + 2 then
        if d.2 = d.1.2 + d.1.1.1 then
          do let z ← Memory.read (wBase d.1.1.1 + (d.1.2 - 2))
             if z = 0 then pure 1 else pure 0
        else pure 0
      else if d.1.1.1 + 2 ≤ d.1.2 ∧ d.1.2 < splitCount d.1.1.1 ∧
          2 ≤ d.2 ∧ d.2 < d.1.1.1 + 2 then
        if d.1.2 - (d.1.1.1 + 2) < d.1.1.2 ∧ d.2 - 2 < d.1.1.2 then
          do let e ← Memory.read (3 + (d.1.2 - (d.1.1.1 + 2)) * d.1.1.1 + (d.2 - 2))
             if e = 1 then pure (d.1.1.1 + 1) else pure 0
        else pure 0
      else pure 0) t ≤ 1 := by
    intro t
    have hleaf : ∀ a c1 c2,
        memoryCost (do let e ← Memory.read a; if e = c1 then pure c2 else pure 0) t ≤ 1 := by
      intro a c1 c2
      exact le_trans (memoryCost_bind_le (mc_read a t) fun _ t' => memoryCost_ite_le (mc_pure _ t')
        (mc_pure 0 t'))
        (by decide)
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    refine memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) ?_
    exact memoryCost_ite_le (memoryCost_ite_le (hleaf _ _ _) (Nat.zero_le _)) (Nat.zero_le _)
  exact le_trans (memoryCost_bind_le (mc_read 0 s) fun _ t => hbody t) (by decide)

private theorem memoryCost_readResCap_le (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readResCap d) s ≤ 4 := by
  unfold readResCap
  refine le_trans (memoryCost_bind_le (memoryCost_readSplitCap_le d s) fun _ t1 =>
    memoryCost_bind_le (mc_read _ t1) fun _ t2 =>
      memoryCost_bind_le (mc_read _ t2) fun _ t3 =>
        memoryCost_ite_le (mc_pure _ t3) (mc_pure 0 t3)) (by decide)

private theorem memoryCost_bfsProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (bfsProg d) s ≤ 80 * (d.1 + 1) ^ 3 := by
  rcases d with ⟨n, m⟩
  dsimp only
  let M := splitCount n
  have hM : M = 2 * (n + 1) := by dsimp only [M, splitCount]; omega
  unfold bfsProg
  dsimp only
  have hlayer : ∀ l t, memoryCost (bfsLayerStep ((n, m), l)) t ≤ 9 * M * M := by
    intro l t
    unfold bfsLayerStep
    dsimp only
    have hmid : ∀ u t', memoryCost (bfsMidStep (((n, m), l), u)) t' ≤ 8 * M := by
      intro u t'
      unfold bfsMidStep
      dsimp only
      have hinn : ∀ v t4, memoryCost (bfsInnerStep ((((n, m), l), u), v)) t4 ≤ 7 := by
        intro v t4
        unfold bfsInnerStep
        dsimp only
        exact le_trans (memoryCost_bind_le (mc_read _ t4) fun _ t5 =>
          memoryCost_bind_le (memoryCost_readResCap_le (((n, m), u), v) t5) fun _ t6 =>
            memoryCost_ite_le
              (memoryCost_bind_le (mc_write _ _ t6) fun _ t7 => (le_refl 1 : memoryCost _ t7 ≤ 1))
              (Nat.zero_le _))
          (by decide)
      exact le_trans (memoryCost_bind_le (mc_read _ t') fun _ t3 =>
        memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of bfsInnerStep 7 (((n, m),
          l), u) hinn M 0 t3)
          fun _ t4 => mc_pure _ t4) (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (mc_read 0 t) fun _ t' =>
      memoryCost_bind_le (memoryCost_iterate_le_of bfsMidStep (8 * M) ((n, m), l) hmid M 0 t')
        fun _ t'' => mc_pure _ t'') (by nlinarith [hM])
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((distBase n, M), M) s) fun _ t1 =>
    memoryCost_bind_le (mc_write _ _ t1) fun _ t2 =>
      memoryCost_bind_le (mc_write _ _ t2) fun _ t3 =>
        memoryCost_bind_le (memoryCost_iterate_le_of bfsLayerStep (9 * M * M) (n,
          m) hlayer (M - 1) 0 t3)
          fun _ t4 => mc_pure () t4) ?_
  dsimp only
  have hsub : M - 1 ≤ M := Nat.sub_le _ _
  have hmul : 9 * M * M * (M - 1) ≤ 9 * M * M * M := Nat.mul_le_mul_left _ hsub
  have hM3 : 9 * M * M * M = 72 * (n + 1) ^ 3 := by rw [hM]; ring
  have hp1 : n + 1 ≤ (n + 1) ^ 3 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 3)
  omega

private theorem memoryCost_minSepProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minSepProg d) s ≤ 180 * (d.1 + 1) ^ 4 := by
  rcases d with ⟨n, m⟩
  dsimp only
  let M := splitCount n
  have hM : M = 2 * (n + 1) := by dsimp only [M, splitCount]; omega
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hp2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 4)
  have hp3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 3 ≤ 4)
  have hn3 : n * ((n + 1) ^ 3) ≤ (n + 1) ^ 4 := by
    calc n * (n + 1) ^ 3 ≤ (n + 1) * (n + 1) ^ 3 := Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = (n + 1) ^ 4 := by ring
  unfold minSepProg
  dsimp only
  have hpush : ∀ cur t3, memoryCost (pushUnitStep (n, cur)) t3 ≤ 5 := by
    intro cur t3
    unfold pushUnitStep
    dsimp only
    exact le_trans (memoryCost_bind_le (mc_read 0 t3) fun _ t4 =>
      memoryCost_ite_le (memoryCost_bind_le (mc_read _ t4) fun _ t5 =>
        memoryCost_ite_le (memoryCost_bind_le (mc_read _ t5) fun _ t6 =>
          memoryCost_ite_le (k := 2) (le_trans (le_refl 1 : memoryCost _ t6 ≤ 1) (by decide))
            (memoryCost_bind_le (k₂ := 1) (mc_read _ t6) fun _ t7 =>
              memoryCost_ite_le (k := 1) (le_refl 1) (Nat.zero_le _)))
          (Nat.zero_le _))
        (Nat.zero_le _)) (by decide)
  have haug : ∀ r t, memoryCost (augRoundStep ((n, m), r)) t ≤ 91 * (n + 1) ^ 3 := by
    intro r t
    unfold augRoundStep
    dsimp only
    have hpow : n + 1 ≤ (n + 1) ^ 3 := by
      simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 3)
    have hbranch : ∀ d1 t'',
        memoryCost (if d1 < splitCount n then do let _ ← iterate pushUnitStep n d1 1; pure (r + 1)
          else pure (r + 1)) t'' ≤ 5 * M := by
      intro d1 t''
      rw [memoryCost_ite]
      split_ifs with hd1
      · refine le_trans (memoryCost_bind_le (memoryCost_iterate_le_of pushUnitStep 5 n hpush d1 1
        t'')
          fun _ t3 => mc_pure _ t3) ?_
        have : 5 * d1 ≤ 5 * M := Nat.mul_le_mul_left 5 (le_of_lt hd1)
        omega
      · exact Nat.zero_le _
    refine le_trans (memoryCost_bind_le (memoryCost_bfsProg_le (n, m) t) fun _ t' =>
      memoryCost_bind_le (mc_read _ t') fun d1 t'' => hbranch d1 t'') ?_
    dsimp only
    omega
  have hext : ∀ vc t4, memoryCost (extractSepStep (n, vc)) t4 ≤ 4 := by
    intro vc t4
    unfold extractSepStep
    exact le_trans (memoryCost_bind_le (mc_read _ t4) fun _ t5 =>
      memoryCost_bind_le (mc_read _ t5) fun _ t6 =>
        memoryCost_bind_le (mc_read _ t6) fun _ t7 =>
          memoryCost_ite_le ((le_refl 1)) ((le_refl 1))) (by decide)
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((flowBase n, 0),
    M * M) s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_iterate_le_of augRoundStep (91 * (n + 1) ^ 3) (n, m) haug n 0 t1)
      fun _ t2 =>
        memoryCost_bind_le (memoryCost_bfsProg_le (n, m) t2) fun _ t3 =>
          memoryCost_bind_le (memoryCost_iterate_le_of extractSepStep 4 n hext n (0, 0) t3)
            fun _ t4 => mc_pure _ t4) ?_
  dsimp only
  have hMM : M * M = 4 * (n + 1) ^ 2 := by rw [hM]; ring
  have h91 : 91 * (n + 1) ^ 3 * n = 91 * (n * (n + 1) ^ 3) := by ring
  omega

private theorem memoryCost_leafProg_le {d : ((ℕ × ℕ) × ℕ) × ℕ} (hL : d.2 ≤ d.1.1.1)
    (s : Memory.State) :
    memoryCost (leafProg d) s ≤ 210 * (d.1.1.1 + 1) ^ 4 := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hL ⊢
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hp2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 4)
  have hunp : ∀ t, memoryCost (unpackGuessProg (n, L)) t ≤ 4 * (n + 1) := by
    intro t
    unfold unpackGuessProg
    dsimp only
    have hstep : ∀ j t2, memoryCost (unpackStep (n, j)) t2 ≤ 3 := fun j t2 => by
      unfold unpackStep
      exact le_trans (memoryCost_bind_le (mc_read _ t2) fun _ t3 =>
        memoryCost_bind_le (mc_read _ t3) fun _ t4 =>
          memoryCost_ite_le ((le_refl 1)) (Nat.zero_le _)) (by decide)
    exact le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((guessBase n, 0), n) t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of unpackStep 3 n hstep L 0 t1) fun _ t2 => mc_pure
        () t2)
      (by dsimp only; omega)
  have hchk : ∀ t, memoryCost (checkProperProg ((n, m), L)) t ≤ 6 * (n + 1) ^ 2 := by
    intro t
    unfold checkProperProg
    have hout : ∀ iok t3, memoryCost (properOuterStep (((n, m), L), iok)) t3 ≤ 3 * L + 2 := by
      intro iok t3
      unfold properOuterStep
      have hinn : ∀ (u du : ℕ) jok t5,
          memoryCost (properInnerStep ((((n, m), u), du), jok)) t5 ≤ 3 := fun u du jok t5 => by
        unfold properInnerStep
        exact le_trans (memoryCost_bind_le (mc_read _ t5) fun _ t6 =>
          memoryCost_bind_le (mc_read _ t6) fun _ t7 =>
            memoryCost_ite_le (memoryCost_bind_le (mc_read _ t7) fun _ t8 =>
              memoryCost_ite_le (mc_pure _ t8) (mc_pure _ t8)) (Nat.zero_le _)) (by decide)
      exact le_trans (memoryCost_bind_le (mc_read _ t3) fun u t4 =>
        memoryCost_bind_le (mc_read _ t4) fun du t5 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of properInnerStep 3 (((n,
            m), u), du)
            (hinn u du) L (0, iok.2) t5) fun _ t6 => mc_pure _ t6) (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (mc_read 0 t) fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of properOuterStep (3 * L + 2) ((n, m),
        L) hout L (0, 1) t2)
        fun _ t3 => mc_pure _ t3) (by nlinarith [hL])
  have hterm : ∀ t, memoryCost (buildTerminalsProg ((n, m), L)) t ≤ 8 * (n + 1) ^ 2 := by
    intro t
    unfold buildTerminalsProg
    dsimp only
    have hout : ∀ v t5, memoryCost (termOuterStep (((n, m), L), v)) t5 ≤ 4 * L + 2 := by
      intro v t5
      unfold termOuterStep
      have hinn : ∀ (cv : ℕ) j t7,
          memoryCost (termInnerStep (((n, m), (v, cv)), j)) t7 ≤ 4 := fun cv j t7 => by
        unfold termInnerStep
        exact le_trans (memoryCost_bind_le (mc_read _ t7) fun _ t8 =>
          memoryCost_bind_le (mc_read _ t8) fun _ t9 =>
            memoryCost_ite_le (memoryCost_bind_le (mc_read _ t9) fun _ t10 =>
              memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
                (Nat.zero_le _)) (Nat.zero_le _)) (by decide)
      exact le_trans (memoryCost_bind_le (mc_read _ t5) fun _ t6 =>
        memoryCost_bind_le (mc_read _ t6) fun cv t7 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_iterate_le_of termInnerStep 4 ((n, m),
            (v, cv))
            (hinn cv) L 0 t7) fun _ t8 => mc_pure _ t8) (Nat.zero_le _)) (by omega)
    exact le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((keepBase n, 0), n) t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_fillRange_le ((flipBase n, 0), n) t1) fun _ t2 =>
        memoryCost_bind_le (memoryCost_iterate_le_of termOuterStep (4 * L + 2) ((n, m),
          L) hout n 0 t2)
          fun _ t3 => mc_pure () t3) (by dsimp only; nlinarith [hL])
  have hcdel : ∀ t, memoryCost (countDelProg (n, L)) t ≤ 2 * (n + 1) := by
    intro t
    unfold countDelProg
    have hstep : ∀ jc t2, memoryCost (countDelStep (n, jc)) t2 ≤ 1 := fun jc t2 => by
      unfold countDelStep
      exact le_trans (memoryCost_bind_le (mc_read _ t2) fun _ t3 => memoryCost_ite_le (mc_pure _
        t3) (mc_pure _ t3))
        (by decide)
    exact le_trans (memoryCost_bind_le (mc_read 0 t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of countDelStep 1 n hstep L (0, 0) t1)
        fun _ t2 => mc_pure _ t2) (by omega)
  have hcom : ∀ t, memoryCost (commitLeafProg n) t ≤ 8 * (n + 1) := by
    intro t
    unfold commitLeafProg
    have hstep : ∀ v t2, memoryCost (commitStep (n, v)) t2 ≤ 7 := fun v t2 => by
      unfold commitStep
      have hcol : ∀ t7 : Memory.State, ∀ c1 c2 c3 c4 c5 : Prop,
          [Decidable c1] → [Decidable c2] → [Decidable c3] → [Decidable c4] → [Decidable c5] →
          memoryCost
            (if c1 then
              if c2 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 1
              else (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else if c3 then
              if c4 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 1
              else (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else if c5 then (fun _ => v + 1) <$> Memory.write (colBase n + v) 0
            else (fun _ => v + 1) <$> Memory.write (colBase n + v) 1) t7 ≤ 1 := by
        intro t7 c1 c2 c3 c4 c5 _ _ _ _ _
        exact memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
          (memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
            (memoryCost_ite_le ((le_refl 1)) ((le_refl 1))))
      exact le_trans (memoryCost_bind_le (mc_read _ t2) fun _ t3 =>
        memoryCost_bind_le (mc_read _ t3) fun _ t4 =>
          memoryCost_bind_le (mc_read _ t4) fun _ t5 =>
            memoryCost_bind_le (mc_read _ t5) fun _ t6 =>
              memoryCost_bind_le (mc_read _ t6) fun _ t7 =>
                memoryCost_ite_le (memoryCost_bind_le (mc_write _ _ t7) fun _ t8 => hcol t8 _ _ _ _
                  _)
                  (memoryCost_bind_le (mc_write _ _ t7) fun _ t8 => hcol t8 _ _ _ _ _)) (by decide)
    exact le_trans (memoryCost_bind_le (mc_read 0 t) fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of commitStep 7 n hstep n 0 t1)
        fun _ t2 => mc_pure () t2) (by omega)
  unfold leafProg
  dsimp only
  refine le_trans (memoryCost_bind_le (hunp s) fun _ t1 =>
    memoryCost_bind_le (hchk t1) fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (hterm t2) fun _ t3 =>
        memoryCost_bind_le (memoryCost_minSepProg_le (n, m) t3) fun _ t4 =>
          memoryCost_bind_le (hcdel t4) fun _ t5 =>
            memoryCost_ite_le (memoryCost_bind_le (hcom t5) fun _ t6 => mc_pure 1 t6) (Nat.zero_le
              _))
        (Nat.zero_le _)) ?_
  dsimp only
  omega

private theorem memoryCost_compressProg_le {d : ((ℕ × ℕ) × ℕ) × ℕ} (hL : d.2 ≤ d.1.1.1)
    (s : Memory.State) :
    memoryCost (compressProg d) s ≤ 215 * 3 ^ d.2 * (d.1.1.1 + 1) ^ 4 := by
  rcases d with ⟨⟨⟨n, k⟩, m⟩, L⟩
  dsimp only at hL ⊢
  have hp1 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hpow : 1 ≤ 3 ^ L := Nat.one_le_pow L 3 (by decide)
  have hodom : ∀ t', memoryCost (incOdomProg (n, L)) t' ≤ 3 * (n + 1) := by
    intro t'
    unfold incOdomProg
    have hstep : ∀ jc t2, memoryCost (incOdomStep (n, jc)) t2 ≤ 2 := fun jc t2 => by
      unfold incOdomStep
      exact le_trans (memoryCost_bind_le (mc_read _ t2) fun _ t3 =>
        memoryCost_ite_le (memoryCost_ite_le ((le_refl 1)) ((le_refl 1)))
          (Nat.zero_le _))
        (by decide)
    exact le_trans (memoryCost_bind_le (mc_read 0 t') fun _ t1 =>
      memoryCost_bind_le (memoryCost_iterate_le_of incOdomStep 2 n hstep L (0, 1) t1)
        fun _ t2 => mc_pure _ t2) (by omega)
  have hguess : ∀ st t, st.1 = 0 →
      memoryCost (guessStep ((((n, k), m), L), st)) t ≤ 214 * (n + 1) ^ 4 := by
    intro st t _
    dsimp only [guessStep]
    refine le_trans (memoryCost_bind_le (mc_read 0 t) fun _ t2 =>
      memoryCost_ite_le
        (memoryCost_bind_le (memoryCost_leafProg_le (d := (((n, k), m), L)) hL t2) fun _ t3 =>
          memoryCost_bind_le (hodom t3) fun _ t4 => mc_pure _ t4)
        (le_trans (memoryCost_bind_le (mc_pure st.2 t2) fun _ t3 =>
          memoryCost_bind_le (hodom t3) fun _ t4 => mc_pure _ t4)
          (by dsimp only; omega))) ?_
    dsimp only
    omega
  unfold compressProg
  dsimp only
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le ((digitBase n, 0), L) s) fun _ t1 =>
    memoryCost_bind_le (memoryCost_boundedWhile_le_of (fun _ (st : ℕ × ℕ) => st.1 = 0) guessStep
      (214 * (n + 1) ^ 4) (((n, k), m), L) hguess (3 ^ L) (0, 0) t1)
      fun _ t2 => mc_pure _ t2) ?_
  dsimp only
  nlinarith [hL]

/-! ### Split-network semantics, BFS, and minimum-separator correctness -/

@[simp, client_simps]
private theorem cr_map {α β : Type} (w : ℕ) (f : α → β) (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).clientResult s (f <$> p) = f ((Memory.spec w).clientResult s p) := by
  induction p generalizing s with
  | pure _ => rfl
  | liftBind _ _ ih => exact ih _ _

private theorem cr_bind_pure {α β : Type} (w : ℕ) (s : Memory.State) (p : Memory.Prog α)
    (f : α → β) :
    (Memory.spec w).clientResult s (p >>= fun x => pure (f x)) =
      f ((Memory.spec w).clientResult s p) := by
  simp only [client_simps]

private theorem cs_bind_pure {α β : Type} (w : ℕ) (s : Memory.State) (p : Memory.Prog α)
    (f : α → β) :
    (Memory.spec w).clientState s (p >>= fun x => pure (f x)) =
      (Memory.spec w).clientState s p := by
  simp only [client_simps]

private theorem fillRange_spec (base val len : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (fillRange ((base, val), len))
    (∀ i < len, s'.mem (base + i) = val) ∧
      (∀ a, (a < base ∨ base + len ≤ a) → s'.mem a = s.mem a) := by
  intro s'
  refine ⟨?_, fun a ha => preservesAt_fillRange ha s⟩
  unfold s' fillRange
  rw [StateTransitionSpec.clientState_bind]
  change ∀ i < len, ((Memory.spec 0).clientState s (iterate fillStep (base, val) len 0)).mem
    (base + i) = val
  have hinv := iterate_invariant_of fillStep (base, val)
    (fun rem (idx : ℕ) t => idx + rem = len ∧ ∀ i < idx, t.mem (base + i) = val)
    (fun rem idx t ⟨hsum, hprev⟩ => by
      unfold fillStep
      rw [clientResult_bind_write, clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun i hi => ?_⟩
      by_cases h : i = idx
      · subst h; simp
      · rw [Function.update_of_ne (by omega)]; exact hprev i (by omega))
    (n := len) (a := 0) (s := s) ⟨Nat.zero_add _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  intro i hi
  exact hinv.2 i (by omega)

private theorem preservesAt_copyRange {a : ℕ} {d : (ℕ × ℕ) × ℕ}
    (hout : a < d.1.2 ∨ d.1.2 + d.2 ≤ a) :
    PreservesAt a (copyRange d) := fun s => by
  unfold copyRange
  rw [StateTransitionSpec.clientState_bind]
  change ((Memory.spec 0).clientState s (iterate copyStep d.1 d.2 0)).mem a = s.mem a
  refine (iterate_invariant_of copyStep d.1
    (fun rem (idx : ℕ) t => idx + rem = d.2 ∧ t.mem a = s.mem a)
    (fun rem idx t ⟨hsum, hmem⟩ => ?_) ⟨Nat.zero_add _, rfl⟩).2
  unfold copyStep
  simp only [client_simps]
  exact ⟨by omega, (Function.update_of_ne (by omega) _ t.mem).trans hmem⟩

private theorem copyRange_spec {srcB dstB len : ℕ} (hdisj : srcB + len ≤ dstB) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (copyRange ((srcB, dstB), len))
    (∀ i < len, s'.mem (dstB + i) = s.mem (srcB + i)) ∧
      (∀ a, (a < dstB ∨ dstB + len ≤ a) → s'.mem a = s.mem a) := by
  intro s'
  refine ⟨?_, fun a ha => preservesAt_copyRange ha s⟩
  unfold s' copyRange
  rw [StateTransitionSpec.clientState_bind]
  change ∀ i < len, ((Memory.spec 0).clientState s (iterate copyStep (srcB, dstB) len 0)).mem
    (dstB + i) = s.mem (srcB + i)
  have hinv := iterate_invariant_of copyStep (srcB, dstB)
    (fun rem (idx : ℕ) t => idx + rem = len ∧
      (∀ i < len, t.mem (srcB + i) = s.mem (srcB + i)) ∧
      (∀ i < idx, t.mem (dstB + i) = s.mem (srcB + i)))
    (fun rem idx t ⟨hsum, hsrc, hdst⟩ => by
      unfold copyStep
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_write,
        clientState_bind_write, clientResult_pure, clientState_pure]
      dsimp only
      refine ⟨by omega, fun i hi => ?_, fun i hi => ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact hsrc i hi
      · by_cases h : i = idx
        · subst h
          simpa using hsrc i (by omega)
        · rw [Function.update_of_ne (by omega)]
          exact hdst i (by omega))
    (n := len) (a := 0) (s := s)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  intro i hi
  exact hinv.2.2 i (by omega)

private def MatrixLoaded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Memory.State) : Prop :=
  ∀ u v : Fin n, s.mem (3 + u.1 * n + v.1) = if G.Adj u v then 1 else 0

private theorem matrixLoaded_init {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    MatrixLoaded G (Memory.State.init (encodeInput G k)) := by
  intro u v
  have hne : 3 + u.1 * n + v.1 ≠ 0 := by omega
  have hsub : 3 + u.1 * n + v.1 - 1 = (u.1 * n + v.1) + 2 := by omega
  have hlt : u.1 * n + v.1 < (encodeAdjMatrix G).length := by
    rw [length_encodeAdjMatrix]
    nlinarith [u.2, v.2]
  change (if 3 + u.1 * n + v.1 = 0 then (encodeInput G k).length
    else (encodeInput G k).getD (3 + u.1 * n + v.1 - 1) 0) = _
  rw [ite_eq_right hne, hsub]
  change (encodeAdjMatrix G).getD (u.1 * n + v.1) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    getElem_encodeAdjMatrix]

private def inIdx {n : ℕ} (v : Fin n) : Fin (splitCount n) :=
  ⟨v.1 + 2, by dsimp only [splitCount]; omega⟩

private def outIdx {n : ℕ} (v : Fin n) : Fin (splitCount n) :=
  ⟨v.1 + n + 2, by dsimp only [splitCount]; omega⟩

private theorem inIdx_injective (n : ℕ) : Function.Injective (inIdx (n := n)) := by
  intro u v h
  exact Fin.ext (by have := congrArg Fin.val h; dsimp only [inIdx] at this; omega)

private noncomputable def splitNet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) : Network (Fin (splitCount n)) where
  s := ⟨0, by dsimp only [splitCount]; omega⟩
  t := ⟨1, by dsimp only [splitCount]; omega⟩
  cap x y :=
    if x.1 = 0 then
      if 2 ≤ y.1 ∧ y.1 < n + 2 then
        if s.mem (keepBase n + (y.1 - 2)) = 1 then n + 1 else 0
      else 0
    else if y.1 = 1 then
      if n + 2 ≤ x.1 ∧ x.1 < splitCount n then
        if s.mem (flipBase n + (x.1 - (n + 2))) = 1 then n + 1 else 0
      else 0
    else if 2 ≤ x.1 ∧ x.1 < n + 2 then
      if y.1 = x.1 + n then
        if s.mem (wBase n + (x.1 - 2)) = 0 then 1 else 0
      else 0
    else if h : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2 then
      let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h; omega⟩
      let v : Fin n := ⟨y.1 - 2, by omega⟩
      if (prefixGraph G m).Adj u v then n + 1 else 0
    else 0

private theorem splitNet_congr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ)
    {s₁ s₂ : Memory.State} (h : ∀ a < flowBase n, s₁.mem a = s₂.mem a) :
    splitNet G m s₁ = splitNet G m s₂ := by
  unfold splitNet
  congr 1
  funext x y
  dsimp only
  by_cases h1 : x.1 = 0
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : 2 ≤ y.1 ∧ y.1 < n + 2
    · rw [ite_eq_left h2, ite_eq_left h2,
        h (keepBase n + (y.1 - 2)) (by dsimp only [keepBase, flowBase]; omega)]
    · rw [ite_eq_right h2, ite_eq_right h2]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : y.1 = 1
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : n + 2 ≤ x.1 ∧ x.1 < splitCount n
      · rw [ite_eq_left h3, ite_eq_left h3,
          h (flipBase n + (x.1 - (n + 2)))
            (by dsimp only [flipBase, flowBase, splitCount] at h3 ⊢; omega)]
      · rw [ite_eq_right h3, ite_eq_right h3]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2
      · rw [ite_eq_left h3, ite_eq_left h3]
        by_cases h4 : y.1 = x.1 + n
        · rw [ite_eq_left h4, ite_eq_left h4,
            h (wBase n + (x.1 - 2)) (by dsimp only [wBase, flowBase]; omega)]
        · rw [ite_eq_right h4, ite_eq_right h4]
      · rw [ite_eq_right h3, ite_eq_right h3]

private theorem cap_splitNet_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) (x y : Fin (splitCount n)) :
    (splitNet G m s).cap x y ≤ n + 1 := by
  unfold splitNet
  dsimp only
  split_ifs <;> omega

private theorem clientResult_readSplitCap {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s : Memory.State} (hG : MatrixLoaded G s) (x y : Fin (splitCount n)) :
    (Memory.spec 0).clientResult s (readSplitCap (((n, m), x.1), y.1)) =
      (splitNet G m s).cap x y ∧
    (Memory.spec 0).clientState s (readSplitCap (((n, m), x.1), y.1)) = s := by
  refine ⟨?_, clientState_readSplitCap _ s⟩
  unfold readSplitCap splitNet
  dsimp only
  rw [clientResult_bind_read]
  by_cases h1 : x.1 = 0
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : 2 ≤ y.1 ∧ y.1 < n + 2
    · rw [ite_eq_left h2, ite_eq_left h2, clientResult_bind_read]
      split_ifs <;> simp only [client_simps]
    · rw [ite_eq_right h2, ite_eq_right h2]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : y.1 = 1
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : n + 2 ≤ x.1 ∧ x.1 < splitCount n
      · rw [ite_eq_left h3, ite_eq_left h3, clientResult_bind_read]
        split_ifs <;> simp only [client_simps]
      · rw [ite_eq_right h3, ite_eq_right h3]; rfl
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2
      · rw [ite_eq_left h3, ite_eq_left h3]
        by_cases h4 : y.1 = x.1 + n
        · rw [ite_eq_left h4, ite_eq_left h4, clientResult_bind_read]
          split_ifs <;> simp only [client_simps]
        · rw [ite_eq_right h4, ite_eq_right h4]; rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2
        · rw [ite_eq_left h4, dite_eq_left h4]
          let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h4; omega⟩
          let v : Fin n := ⟨y.1 - 2, by omega⟩
          have hmem := hG u v
          dsimp only [u, v] at hmem
          by_cases hm : x.1 - (n + 2) < m ∧ y.1 - 2 < m
          · rw [ite_eq_left hm, clientResult_bind_read, hmem]
            by_cases hadj : G.Adj u v
            · have hp : (prefixGraph G m).Adj u v := ⟨hadj, hm.1, hm.2⟩
              change (Memory.spec 0).clientResult s
                (if (if G.Adj u v then 1 else 0) = 1 then pure (n + 1) else pure 0) =
                if (prefixGraph G m).Adj u v then n + 1 else 0
              simp only [hadj, hp, ↓reduceIte, client_simps]
            · have hp : ¬ (prefixGraph G m).Adj u v := fun h => hadj h.1
              change (Memory.spec 0).clientResult s
                (if (if G.Adj u v then 1 else 0) = 1 then pure (n + 1) else pure 0) =
                if (prefixGraph G m).Adj u v then n + 1 else 0
              simp only [hadj, hp, ↓reduceIte, Nat.zero_ne_one, client_simps]
          · rw [ite_eq_right hm]
            have hp : ¬ (prefixGraph G m).Adj u v := fun h => hm ⟨h.2.1, h.2.2⟩
            change (Memory.spec 0).clientResult s (pure 0) =
              if (prefixGraph G m).Adj u v then n + 1 else 0
            simp only [hp, ↓reduceIte, client_simps]
        · rw [ite_eq_right h4, dite_eq_right h4]; rfl

private def FlowStored {n : ℕ} {N : Network (Fin (splitCount n))}
    (f : N.Flow) (s : Memory.State) : Prop :=
  ∀ x y : Fin (splitCount n), s.mem (flowBase n + x.1 * splitCount n + y.1) = f x y

private theorem clientResult_readResCap {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ s : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    {f : (splitNet G m s₀).Flow} (hf : FlowStored f s) (x y : Fin (splitCount n)) :
    (Memory.spec 0).clientResult s (readResCap (((n, m), x.1), y.1)) = f.resCap x y ∧
      (Memory.spec 0).clientState s (readResCap (((n, m), x.1), y.1)) = s := by
  have hG' : MatrixLoaded G s := fun u v => by
    rw [hlow _ (by dsimp only [flowBase]; nlinarith [u.2, v.2]), hG u v]
  obtain ⟨hcap_r, hcap_s⟩ := clientResult_readSplitCap (m := m) hG' x y
  rw [splitNet_congr G m hlow] at hcap_r
  unfold readResCap
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind, hcap_r, hcap_s]
  dsimp only
  rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
    clientState_bind_read, hf x y, hf y x]
  have hc1 := cap_splitNet_le G m s₀ x y
  have hc2 := cap_splitNet_le G m s₀ y x
  have hle1 := f.le_cap x y
  have hle2 := f.le_cap y x
  have hcond : (splitNet G m s₀).cap x y ≤ n + 1 ∧ f x y ≤ (splitNet G m s₀).cap x y ∧
      f y x ≤ n + 1 := ⟨hc1, hle1, hle2.trans hc2⟩
  rw [ite_eq_left hcond, clientResult_pure, clientState_pure]
  exact ⟨rfl, rfl⟩

private def BfsLayerInv {n : ℕ} {N : Network (Fin (splitCount n))}
    (f : N.Flow) (layer : ℕ) (t : Memory.State) : Prop :=
  (∀ x : Fin (splitCount n),
    (f.resDist x ≤ layer → t.mem (distBase n + x.1) = f.resDist x) ∧
    (layer < f.resDist x → t.mem (distBase n + x.1) = splitCount n)) ∧
  (∀ x : Fin (splitCount n),
    0 < t.mem (distBase n + x.1) → t.mem (distBase n + x.1) < splitCount n →
    ∃ u : Fin (splitCount n),
      t.mem (parBase n + x.1) = u.1 ∧
      f.resDist u + 1 = f.resDist x ∧
      0 < f.resCap u x)

private theorem bfsMid_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m layer : ℕ} {s₀ s st : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    (f : (splitNet G m s₀).Flow) (hf : FlowStored f s)
    (hlayer_lt : layer + 1 < splitCount n)
    (hst_low : ∀ a < distBase n, st.mem a = s.mem a)
    (hlinv : BfsLayerInv f layer st) :
    let t_end :=
      (Memory.spec 0).clientState st (iterate bfsMidStep ((n, m), layer) (splitCount n) 0)
    (Memory.spec 0).clientResult st (iterate bfsMidStep ((n, m), layer) (splitCount n) 0) =
      splitCount n ∧
    (∀ a < distBase n, t_end.mem a = s.mem a) ∧
    BfsLayerInv f (layer + 1) t_end := by
  let M := splitCount n
  have hmid := iterate_invariant_of bfsMidStep ((n, m), layer)
    (fun urem (u : ℕ) t' =>
      u + urem = M ∧
      (∀ a < distBase n, t'.mem a = s.mem a) ∧
      (∀ x : Fin M, f.resDist x ≤ layer → t'.mem (distBase n + x.1) = f.resDist x) ∧
      (∀ x : Fin M, layer + 1 < f.resDist x → t'.mem (distBase n + x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        t'.mem (distBase n + x.1) = layer + 1 ∨ t'.mem (distBase n + x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
        t'.mem (distBase n + x.1) = layer + 1) ∧
      (∀ x : Fin M, 0 < t'.mem (distBase n + x.1) → t'.mem (distBase n + x.1) < M →
        ∃ p : Fin M, t'.mem (parBase n + x.1) = p.1 ∧
          f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
    (fun urem u t' ⟨husum, ht_low, hd_le, hd_gt, hd_eq, hd_found, hpar⟩ => by
      have hu_lt : u < M := by omega
      let uFin : Fin M := ⟨u, hu_lt⟩
      unfold bfsMidStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hdu : t'.mem (distBase n + u) = layer
      · rw [ite_eq_left hdu, cr_bind_pure, cs_bind_pure]
        have hres_u : f.resDist uFin = layer := by
          by_contra hne
          rcases lt_trichotomy (f.resDist uFin) layer with hlt | heq | hgt
          · have h1 : t'.mem (distBase n + u) = f.resDist uFin := hd_le uFin (le_of_lt hlt)
            omega
          · exact hne heq
          · by_cases h1 : f.resDist uFin = layer + 1
            · rcases hd_eq uFin h1 with h | h
              · have h' : t'.mem (distBase n + u) = layer + 1 := h; omega
              · have h' : t'.mem (distBase n + u) = M := h; omega
            · have h2 : t'.mem (distBase n + u) = M := hd_gt uFin (by omega)
              omega
        have hinn := iterate_invariant_of bfsInnerStep (((n, m), layer), u)
          (fun vrem (v : ℕ) t'' =>
            v + vrem = M ∧
            (∀ a < distBase n, t''.mem a = s.mem a) ∧
            (∀ x : Fin M, f.resDist x ≤ layer → t''.mem (distBase n + x.1) = f.resDist x) ∧
            (∀ x : Fin M, layer + 1 < f.resDist x → t''.mem (distBase n + x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              t''.mem (distBase n + x.1) = layer + 1 ∨ t''.mem (distBase n + x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
              t''.mem (distBase n + x.1) = layer + 1) ∧
            (∀ x : Fin M, x.1 < v → 0 < f.resCap uFin x → f.resDist x = layer + 1 →
              t''.mem (distBase n + x.1) = layer + 1) ∧
            (∀ x : Fin M, 0 < t''.mem (distBase n + x.1) → t''.mem (distBase n + x.1) < M →
              ∃ p : Fin M, t''.mem (parBase n + x.1) = p.1 ∧
                f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
          (fun vrem v t'' ⟨hvsum, hi_low, hi_le, hi_gt, hi_eq, hi_found, hi_cur, hi_par⟩ => by
            have hv_lt : v < M := by omega
            let vFin : Fin M := ⟨v, hv_lt⟩
            have hf'' : FlowStored f t'' := fun x y => by
              rw [hi_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf x y]
            have hlow'' : ∀ a < flowBase n, t''.mem a = s₀.mem a := fun a ha => by
              rw [hi_low _ (by dsimp only [distBase]; omega), hlow a ha]
            obtain ⟨hrc_r, hrc_s⟩ := clientResult_readResCap hG hlow'' hf'' uFin vFin
            unfold bfsInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind, clientState_bind]
            have hrc_r' : (Memory.spec 0).clientResult t'' (readResCap (((n, m), u), v)) =
                f.resCap uFin vFin := hrc_r
            have hrc_s' : (Memory.spec 0).clientState t'' (readResCap (((n, m), u), v)) =
                t'' := hrc_s
            rw [hrc_r', hrc_s']
            by_cases hcond : t''.mem (distBase n + v) = M ∧ 0 < f.resCap uFin vFin
            · rw [ite_eq_left hcond, clientResult_bind_write, clientState_bind_write,
              clientResult_bind_write,
                clientState_bind_write]
              simp only [client_simps]
              have hv_res : f.resDist vFin = layer + 1 := by
                have htri := f.resDist_le_add_one_of_pos_resCap hcond.2
                rw [hres_u] at htri
                have hnle : ¬ f.resDist vFin ≤ layer := fun hle => by
                  have h1 : t''.mem (distBase n + v) = f.resDist vFin := hi_le vFin hle
                  omega
                omega
              refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, fun x hx => ?_,
                fun x hx => ?_, fun x hx hex => ?_, fun x hx hpos hx1 => ?_,
                fun x hpos hlt => ?_⟩
              · rw [Function.update_of_ne (by dsimp only [parBase]; omega),
                  Function.update_of_ne (by omega)]
                exact hi_low a ha
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
                  Function.update_of_ne (by omega)]
                exact hi_le x hx
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
                  Function.update_of_ne (by omega)]
                exact hi_gt x hx
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · left; rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact hi_eq x hx
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact hi_found x hx hex
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]
                  exact hi_cur x (by omega) hpos hx1
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                  at hpos hlt
                by_cases hxv : x.1 = v
                · have hxeq : x = vFin := Fin.ext hxv
                  subst hxeq
                  exact ⟨uFin, by dsimp only [vFin]; rw [Function.update_self],
                    by rw [hres_u, hv_res], hcond.2⟩
                · rw [Function.update_of_ne (by omega)] at hpos hlt
                  obtain ⟨p, hp1, hp2, hp3⟩ := hi_par x hpos hlt
                  exact ⟨p, by
                    rw [Function.update_of_ne (by omega),
                      Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                    exact hp1, hp2, hp3⟩
            · rw [ite_eq_right hcond]
              simp only [client_simps]
              refine ⟨by omega, hi_low, hi_le, hi_gt, hi_eq, hi_found,
                fun x hx hpos hx1 => ?_, hi_par⟩
              by_cases hxv : x.1 = v
              · have hxeq : x = vFin := Fin.ext hxv
                subst hxeq
                rcases hi_eq vFin hx1 with h1 | hM'
                · exact h1
                · exact absurd ⟨hM', hpos⟩ hcond
              · exact hi_cur x (by omega) hpos hx1)
          (n := M) (a := 0) (s := t')
          ⟨Nat.zero_add _, ht_low, hd_le, hd_gt, hd_eq, hd_found,
            fun _ hx => absurd hx (Nat.not_lt_zero _), hpar⟩
        obtain ⟨hvsum_end, h1, h2, h3, h4, h5, h6, h7⟩ := hinn
        have hv_end : (Memory.spec 0).clientResult t'
            (iterate bfsInnerStep (((n, m), layer), u) M 0) = M := by omega
        rw [hv_end] at h6
        refine ⟨by omega, h1, h2, h3, h4, fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, h7⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          exact h6 x x.2 hrc' hx
        · exact h5 x hx ⟨u', by omega, hru', hrc'⟩
      · rw [ite_eq_right hdu]
        simp only [client_simps]
        refine ⟨by omega, ht_low, hd_le, hd_gt, hd_eq,
          fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, hpar⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          have h1 : t'.mem (distBase n + u) = f.resDist uFin := hd_le uFin (le_of_eq hru')
          omega
        · exact hd_found x hx ⟨u', by omega, hru', hrc'⟩)
    (n := M) (a := 0) (s := st)
    ⟨Nat.zero_add _, hst_low, fun x hx => (hlinv.1 x).1 hx,
      fun x hx => (hlinv.1 x).2 (by omega),
      fun x hx => Or.inr ((hlinv.1 x).2 (by omega)),
      fun _ _ ⟨_, hu, _⟩ => absurd hu (Nat.not_lt_zero _),
      hlinv.2⟩
  obtain ⟨husum_end, hm_low, hm_le, hm_gt, _, hm_found, hm_par⟩ := hmid
  have hu_end : (Memory.spec 0).clientResult st
      (iterate bfsMidStep ((n, m), layer) M 0) = M := by omega
  rw [hu_end] at hm_found
  refine ⟨hu_end, hm_low, ⟨fun x => ⟨fun hx => ?_, fun hx => hm_gt x hx⟩, hm_par⟩⟩
  by_cases hx_eq : f.resDist x = layer + 1
  · have hcard : layer + 1 < Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hlayer_lt
    obtain ⟨u', hru', hrc'⟩ := f.exists_pred_of_resDist_eq_succ hcard hx_eq
    rw [hx_eq]
    exact hm_found x hx_eq ⟨u', u'.2, hru', hrc'⟩
  · exact hm_le x (by omega)

private theorem bfsProg_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ s : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    (f : (splitNet G m s₀).Flow) (hf : FlowStored f s) :
    let t := (Memory.spec 0).clientState s (bfsProg (n, m))
    (∀ a < distBase n, t.mem a = s.mem a) ∧
      (∀ x : Fin (splitCount n), t.mem (distBase n + x.1) = f.resDist x) ∧
      (∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
        ∃ u : Fin (splitCount n),
          t.mem (parBase n + x.1) = u.1 ∧
          f.resDist u + 1 = f.resDist x ∧
          0 < f.resCap u x) := by
  intro t
  have hpres : ∀ a < distBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_bfsProg (Or.inl ha) s
  refine ⟨hpres, ?_⟩
  let M := splitCount n
  let N := splitNet G m s₀
  set s1 := (Memory.spec 0).clientState s (fillRange ((distBase n, M), M))
  have hs1 := fillRange_spec (distBase n) M M s
  set s2 : Memory.State :=
    ⟨Function.update (Function.update s1.mem (distBase n) 0) (parBase n) 0, s1.frontier⟩
  have hs2_low : ∀ a < distBase n, s2.mem a = s.mem a := by
    intro a ha
    have hne1 : a ≠ parBase n := by dsimp only [parBase, splitCount]; omega
    have hne2 : a ≠ distBase n := by omega
    dsimp only [s2]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact hs1.2 a (Or.inl ha)
  have hinv0 : BfsLayerInv f 0 s2 := by
    refine ⟨fun x => ⟨fun hle => ?_, fun hgt => ?_⟩, fun x hpos hlt => ?_⟩
    · have hx0 : f.resDist x = 0 := Nat.eq_zero_of_le_zero hle
      have hxs : x = N.s := f.eq_source_of_resDist_eq_zero hx0
      have hxval : x.1 = 0 := by rw [hxs]; rfl
      dsimp only [s2]
      rw [hxval, add_zero, Function.update_of_ne
        (by dsimp only [parBase, splitCount]; omega), Function.update_self, hx0]
    · have hxs : x ≠ N.s := fun h => by rw [h, f.resDist_source] at hgt; omega
      have hxne : x.1 ≠ 0 := fun h => hxs (Fin.ext h)
      dsimp only [s2]
      rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
        Function.update_of_ne (by omega)]
      exact hs1.1 x.1 x.2
    · by_cases hx0 : x.1 = 0
      · dsimp only [s2] at hpos
        rw [hx0, add_zero, Function.update_of_ne
          (by dsimp only [parBase, splitCount]; omega), Function.update_self] at hpos
        omega
      · dsimp only [s2] at hlt
        rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
          Function.update_of_ne (by omega), hs1.1 x.1 x.2] at hlt
        omega
  have hlayers := iterate_invariant_of bfsLayerStep (n, m)
    (fun rem (layer : ℕ) st =>
      layer + rem = M - 1 ∧ (∀ a < distBase n, st.mem a = s.mem a) ∧ BfsLayerInv f layer st)
    (fun rem layer st ⟨hsum, hst_low, hlinv⟩ => by
      have hlayer_lt : layer + 1 < M := by dsimp only [M, splitCount] at hsum ⊢; omega
      obtain ⟨_, hm_low, hm_inv⟩ := bfsMid_spec hG hlow f hf hlayer_lt hst_low hlinv
      unfold bfsLayerStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, cr_bind_pure, cs_bind_pure]
      exact ⟨by omega, hm_low, hm_inv⟩)
    (n := M - 1) (a := 0) (s := s2) ⟨Nat.zero_add _, hs2_low, hinv0⟩
  obtain ⟨hsum_end, _, hinv_end⟩ := hlayers
  set s3 := (Memory.spec 0).clientState s2 (iterate bfsLayerStep (n, m) (M - 1) 0)
  have hlay_eq : ((Memory.spec 0).clientResult s2 (iterate bfsLayerStep (n, m) (M - 1) 0)) =
      M - 1 := by omega
  rw [hlay_eq] at hinv_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (bfsProg (n, m)) = s3
    unfold bfsProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind_write, clientState_bind_write,
      cs_bind_pure]
  rw [ht_eq]
  have hdist_all : ∀ x : Fin M, s3.mem (distBase n + x.1) = f.resDist x := by
    intro x
    have hle_card : f.resDist x ≤ M := by simpa [Fintype.card_fin] using f.resDist_le_card x
    by_cases hx : f.resDist x ≤ M - 1
    · exact (hinv_end.1 x).1 hx
    · have hxM : f.resDist x = M := by dsimp only [M, splitCount] at hle_card hx ⊢; omega
      rw [(hinv_end.1 x).2 (by dsimp only [M, splitCount] at hxM ⊢; omega), hxM]
  refine ⟨hdist_all, fun x hpos hlt => ?_⟩
  rw [← hdist_all x] at hpos hlt
  exact hinv_end.2 x hpos hlt

private def buildPath {M : ℕ} (parOf : Fin M → Fin M) : ℕ → Fin M → List (Fin M)
  | 0, cur => [cur]
  | rem + 1, cur => buildPath parOf rem (parOf cur) ++ [cur]

private theorem buildPath_ne_nil {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, buildPath parOf rem cur ≠ []
  | 0, _ => List.cons_ne_nil _ _
  | _ + 1, cur => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil cur [])

private theorem buildPath_getLast? {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, (buildPath parOf rem cur).getLast? = some cur
  | 0, _ => rfl
  | rem + 1, cur => by
    unfold buildPath
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil cur [])]
    rfl

private theorem buildPath_props {M : ℕ} {N : Network (Fin M)} (f : N.Flow)
    (parOf : Fin M → Fin M)
    (hpar : ∀ x : Fin M, 0 < f.resDist x → f.resDist x < M →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x) :
    ∀ rem (cur : Fin M), rem < M → f.resDist cur = rem →
      (buildPath parOf rem cur).head? = some N.s ∧
      (∀ z ∈ buildPath parOf rem cur, f.resDist z ≤ rem) ∧
      (buildPath parOf rem cur).Nodup ∧
      (∀ e ∈ pathArcs (buildPath parOf rem cur), 1 ≤ f.resCap e.1 e.2)
  | 0, cur, _, hcur => by
    have hs : cur = N.s := f.eq_source_of_resDist_eq_zero hcur
    refine ⟨by simp [buildPath, hs], ?_, List.nodup_singleton cur, by simp [buildPath]⟩
    intro z hz
    simp only [buildPath, List.mem_singleton] at hz
    subst hz
    exact le_of_eq hcur
  | rem + 1, cur, hrem, hcur => by
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    obtain ⟨hhead, hle, hnd, harcs⟩ := buildPath_props f parOf hpar rem (parOf cur)
      (by omega) hp_rem
    have hne := buildPath_ne_nil parOf rem (parOf cur)
    have hlast := buildPath_getLast? parOf rem (parOf cur)
    unfold buildPath
    refine ⟨by rw [List.head?_append_of_ne_nil _ hne]; exact hhead, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact (hle z hz1).trans (Nat.le_succ rem)
      · simp only [List.mem_singleton] at hz2; subst hz2; omega
    · refine List.Nodup.append hnd (List.nodup_singleton cur) fun a ha hb => ?_
      simp only [List.mem_singleton] at hb
      subst hb
      have := hle a ha
      omega
    · rw [pathArcs_append_singleton hne hlast]
      intro e he
      rcases List.mem_append.mp he with he1 | he2
      · exact harcs e he1
      · simp only [List.mem_singleton] at he2; subst he2; exact hrc_p

private theorem iterate_pushUnitStep_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ : Memory.State} (f : (splitNet G m s₀).Flow)
    (parOf : Fin (splitCount n) → Fin (splitCount n))
    (hpar : ∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x) :
    ∀ rem (cur : Fin (splitCount n)) (u_st : Memory.State),
      rem < splitCount n → f.resDist cur = rem →
      (∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
        u_st.mem (parBase n + x.1) = (parOf x).1) →
      (∀ x y : Fin (splitCount n),
        ((x, y) ∈ pathArcs (buildPath parOf rem cur) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem cur)) →
        u_st.mem (flowBase n + x.1 * splitCount n + y.1) = f x y) →
      let t_end := (Memory.spec 0).clientState u_st (iterate pushUnitStep n rem cur.1)
      (∀ a < flowBase n, t_end.mem a = u_st.mem a) ∧
      (∀ x y : Fin (splitCount n),
        t_end.mem (flowBase n + x.1 * splitCount n + y.1) =
          if (x, y) ∈ pathArcs (buildPath parOf rem cur) then
            f x y + (1 - min 1 (f y x))
          else if (y, x) ∈ pathArcs (buildPath parOf rem cur) then
            f x y - min 1 (f x y)
          else
            u_st.mem (flowBase n + x.1 * splitCount n + y.1))
  | 0, cur, u_st, _, _, _, _ => by
    refine ⟨fun _ _ => rfl, fun x y => ?_⟩
    simp only [iterate, buildPath, pathArcs_singleton, List.not_mem_nil, ↓reduceIte]
    rfl
  | rem + 1, cur, u_st, hrem, hcur, hp_mem, hf_sub => by
    let M := splitCount n
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hne_pc : parOf cur ≠ cur := fun h => by rw [h] at hp_rem; omega
    have hpar_val : u_st.mem (parBase n + cur.1) = (parOf cur).1 :=
      hp_mem cur (by omega) (by omega)
    have hne_path := buildPath_ne_nil parOf rem (parOf cur)
    have hlast_path := buildPath_getLast? parOf rem (parOf cur)
    have harcs_eq : pathArcs (buildPath parOf (rem + 1) cur) =
        pathArcs (buildPath parOf rem (parOf cur)) ++ [(parOf cur, cur)] := by
      rw [buildPath]
      exact pathArcs_append_singleton hne_path hlast_path
    have hf_rev : u_st.mem (flowBase n + cur.1 * M + (parOf cur).1) = f cur (parOf cur) :=
      hf_sub cur (parOf cur) (Or.inr (by rw [harcs_eq]; simp))
    have hf_fwd : u_st.mem (flowBase n + (parOf cur).1 * M + cur.1) = f (parOf cur) cur :=
      hf_sub (parOf cur) cur (Or.inl (by rw [harcs_eq]; simp))
    have hstep_res_state :
        (Memory.spec 0).clientResult u_st (pushUnitStep (n, cur.1)) = (parOf cur).1 ∧
        let u1 := (Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))
        (∀ a < flowBase n, u1.mem a = u_st.mem a) ∧
        (∀ x : Fin M, u1.mem (parBase n + x.1) = u_st.mem (parBase n + x.1)) ∧
        (∀ x y : Fin M,
          u1.mem (flowBase n + x.1 * M + y.1) =
            if (x, y) = (parOf cur, cur) then f x y + (1 - min 1 (f y x))
            else if (y, x) = (parOf cur, cur) then f x y - min 1 (f x y)
            else u_st.mem (flowBase n + x.1 * M + y.1)) := by
      have hlow1 : ∀ a < flowBase n,
          ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem a = u_st.mem a :=
        fun a ha => preservesAt_pushUnitStep (Or.inl ha) u_st
      have hpar1 : ∀ x : Fin M,
          ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem (parBase n + x.1) =
            u_st.mem (parBase n + x.1) :=
        fun x => preservesAt_pushUnitStep (Or.inr (by dsimp only [parBase]; omega)) u_st
      refine ⟨?_, hlow1, hpar1, ?_⟩
      · unfold pushUnitStep
        dsimp only
        rw [clientResult_bind_read, ite_eq_left cur.2, clientResult_bind_read, hpar_val,
          ite_eq_left (parOf cur).2,
          clientResult_bind_read, hf_rev]
        by_cases hrev0 : 0 < f cur (parOf cur)
        · rw [ite_eq_left hrev0, clientResult_bind_write]; rfl
        · have hcap_le := cap_splitNet_le G m s₀ (parOf cur) cur
          have hf_lt_cap : f (parOf cur) cur ≤ n := by unfold Network.Flow.resCap at hrc_p; omega
          rw [ite_eq_right hrev0, clientResult_bind_read, hf_fwd, ite_eq_left hf_lt_cap,
            clientResult_bind_write]; rfl
      · intro x y
        dsimp only [M] at x y ⊢
        change ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem
          (flowBase n + x.1 * M + y.1) = _
        unfold pushUnitStep
        dsimp only
        rw [clientState_bind_read, ite_eq_left cur.2, clientState_bind_read, hpar_val,
          ite_eq_left (parOf cur).2,
          clientState_bind_read, hf_rev]
        by_cases hrev0 : 0 < f cur (parOf cur)
        · rw [ite_eq_left hrev0, clientState_bind_write]
          change Function.update u_st.mem (flowBase n + cur.1 * M + (parOf cur).1)
            (f cur (parOf cur) - 1) (flowBase n + x.1 * M + y.1) = _
          by_cases hxy : (x, y) = (parOf cur, cur)
          · injection hxy with hx hy
            rw [hx, hy]
            simp only [↓reduceIte]
            have hne_addr : flowBase n + (parOf cur).1 * M + cur.1 ≠
                flowBase n + cur.1 * M + (parOf cur).1 := by
              intro h
              have heq := finProdFinEquiv.injective
                (a₁ := (parOf cur, cur)) (a₂ := (cur, parOf cur))
                (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
              exact hne_pc (Prod.mk.inj heq).1
            have hmin1 : min 1 (f cur (parOf cur)) = 1 := min_eq_left hrev0
            rw [Function.update_of_ne hne_addr, hf_fwd, hmin1]
            omega
          · simp only [hxy, ↓reduceIte]
            by_cases hyx : (y, x) = (parOf cur, cur)
            · injection hyx with hy hx
              rw [hy, hx]
              simp only [↓reduceIte]
              have hmin1 : min 1 (f cur (parOf cur)) = 1 := min_eq_left hrev0
              rw [Function.update_self, hmin1]
            · simp only [hyx, ↓reduceIte]
              have hne_addr : flowBase n + x.1 * M + y.1 ≠
                  flowBase n + cur.1 * M + (parOf cur).1 := by
                intro h
                have heq := finProdFinEquiv.injective
                  (a₁ := (x, y)) (a₂ := (cur, parOf cur))
                  (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
                obtain ⟨hx, hy⟩ := Prod.mk.inj heq
                exact hyx (Prod.ext hy hx)
              exact Function.update_of_ne hne_addr _ _
        · have hrev_eq : f cur (parOf cur) = 0 := by omega
          have hcap_le := cap_splitNet_le G m s₀ (parOf cur) cur
          have hf_lt_cap : f (parOf cur) cur ≤ n := by
            unfold Network.Flow.resCap at hrc_p
            omega
          rw [ite_eq_right hrev0, clientState_bind_read, hf_fwd, ite_eq_left hf_lt_cap,
            clientState_bind_write]
          change Function.update u_st.mem (flowBase n + (parOf cur).1 * M + cur.1)
            (f (parOf cur) cur + 1) (flowBase n + x.1 * M + y.1) = _
          by_cases hxy : (x, y) = (parOf cur, cur)
          · injection hxy with hx hy
            rw [hx, hy]
            have hmin0 : min 1 (0 : ℕ) = 0 := min_eq_right (Nat.zero_le 1)
            simp only [↓reduceIte, hrev_eq, hmin0, Nat.sub_zero]
            rw [Function.update_self]
          · simp only [hxy, ↓reduceIte]
            have hne_addr : flowBase n + x.1 * M + y.1 ≠
                flowBase n + (parOf cur).1 * M + cur.1 := by
              intro h
              have heq := finProdFinEquiv.injective
                (a₁ := (x, y)) (a₂ := (parOf cur, cur))
                (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
              exact hxy heq
            rw [Function.update_of_ne hne_addr]
            by_cases hyx : (y, x) = (parOf cur, cur)
            · injection hyx with hy hx
              rw [hy, hx]
              simp [hf_rev, hrev_eq]
            · simp only [hyx, ↓reduceIte]; rfl
    obtain ⟨hres1, hlow1, hpar1, hflow1⟩ := hstep_res_state
    set u1 := (Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))
    obtain ⟨_, hle_rem, _, _⟩ := buildPath_props f parOf hpar rem (parOf cur) (by omega) hp_rem
    have hdisj : ∀ a b : Fin M, (a, b) ∈ pathArcs (buildPath parOf rem (parOf cur)) →
        a ≠ cur ∧ b ≠ cur := by
      intro a b hab
      have ha := hle_rem a (fst_mem_of_mem_pathArcs hab)
      have hb := hle_rem b (snd_mem_of_mem_pathArcs hab)
      exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩
    have hf_sub1 : ∀ x y : Fin M,
        ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))) →
        u1.mem (flowBase n + x.1 * M + y.1) = f x y := by
      intro x y hmem
      rw [hflow1 x y]
      rcases hmem with hxy | hyx
      · obtain ⟨_, hyc⟩ := hdisj x y hxy
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hyc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj x y hxy).1 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inl (by rw [harcs_eq]; exact List.mem_append_left _ hxy))
      · obtain ⟨hxc, _⟩ := hdisj y x hyx
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hxc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj y x hyx).2 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inr (by rw [harcs_eq]; exact List.mem_append_left _ hyx))
    have hih := iterate_pushUnitStep_spec f parOf hpar rem (parOf cur) u1 (by omega) hp_rem
      (fun x hx1 hx2 => (hpar1 x).trans (hp_mem x hx1 hx2)) hf_sub1
    dsimp only [iterate]
    rw [StateTransitionSpec.clientState_bind, hres1]
    refine ⟨fun a ha => (hih.1 a ha).trans (hlow1 a ha), fun x y => ?_⟩
    rw [hih.2 x y, hflow1 x y, harcs_eq]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h1 : (x, y) ∈ pathArcs (buildPath parOf rem (parOf cur))
    · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
    · by_cases h2 : (x, y) = (parOf cur, cur)
      · have h3 : (y, x) ∉ pathArcs (buildPath parOf rem (parOf cur)) := fun h =>
          (hdisj y x h).1 (Prod.mk.inj h2).2
        rw [ite_eq_right h1, ite_eq_right h3, ite_eq_left h2, ite_eq_left (Or.inr h2)]
      · have h12 : ¬ ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
            (x, y) = (parOf cur, cur)) := not_or.mpr ⟨h1, h2⟩
        rw [ite_eq_right h1, ite_eq_right h12]
        by_cases h3 : (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))
        · rw [ite_eq_left h3, ite_eq_left (Or.inl h3)]
        · by_cases h4 : (y, x) = (parOf cur, cur)
          · rw [ite_eq_right h3, ite_eq_right h2, ite_eq_left h4, ite_eq_left (Or.inr h4)]
          · have h34 : ¬ ((y, x) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
                (y, x) = (parOf cur, cur)) := not_or.mpr ⟨h3, h4⟩
            rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h4, ite_eq_right h34]

private def midCut (n : ℕ) : Finset (Fin (splitCount n)) :=
  Finset.univ.filter fun x => x.1 = 0 ∨ (2 ≤ x.1 ∧ x.1 < n + 2)

private theorem isCut_midCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) :
    (splitNet G m s).IsCut (midCut n) := by
  refine ⟨?_, ?_⟩
  · simp [midCut, splitNet]
  · simp [midCut, splitNet]

private theorem cutCapacity_midCut_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) :
    (splitNet G m s).cutCapacity (midCut n) ≤ n := by
  let N := splitNet G m s
  have hinner : ∀ x ∈ midCut n,
      (∑ y ∈ Finset.univ \ midCut n, N.cap x y) ≤ if x.1 = 0 then 0 else 1 := by
    intro x hx
    simp only [midCut, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hx0 | hx_in
    · rw [ite_eq_left hx0]
      refine le_of_eq (Finset.sum_eq_zero fun y hy => ?_)
      simp only [midCut, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      unfold N splitNet
      dsimp only
      rw [ite_eq_left hx0, ite_eq_right (fun h => hy (Or.inr h))]
    · have hxne : x.1 ≠ 0 := by omega
      rw [ite_eq_right hxne]
      let y0 : Fin (splitCount n) := ⟨x.1 + n, by dsimp only [splitCount]; omega⟩
      have hsub : (∑ y ∈ Finset.univ \ midCut n, N.cap x y) ≤ N.cap x y0 := by
        have hzero : ∀ y ∈ Finset.univ \ midCut n, y ≠ y0 → N.cap x y = 0 := by
          intro y hy hne
          simp only [midCut, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hy1 : y.1 ≠ 1 → ¬ y.1 = x.1 + n → N.cap x y = 0 := by
            intro hy_not1 hy_not_add
            unfold N splitNet
            dsimp only
            rw [ite_eq_right hxne, ite_eq_right hy_not1, ite_eq_left hx_in,
              ite_eq_right hy_not_add]
          by_cases hy_eq1 : y.1 = 1
          · unfold N splitNet
            dsimp only
            rw [ite_eq_right hxne, ite_eq_left hy_eq1, ite_eq_right (by omega)]
          · exact hy1 hy_eq1 (fun h => hne (Fin.ext h))
        by_cases hy0_mem : y0 ∈ Finset.univ \ midCut n
        · rw [Finset.sum_eq_single y0 (fun y hy hne => hzero y hy hne)
            (fun h => absurd hy0_mem h)]
        · rw [Finset.sum_eq_zero (fun y hy => hzero y hy (fun h => hy0_mem (h ▸ hy)))]
          exact Nat.zero_le _
      refine hsub.trans ?_
      unfold N splitNet
      dsimp only [y0]
      rw [ite_eq_right hxne, ite_eq_right (by omega), ite_eq_left hx_in, ite_eq_left rfl]
      split_ifs <;> omega
  calc N.cutCapacity (midCut n)
      ≤ ∑ x ∈ midCut n, (if x.1 = 0 then 0 else 1) := Finset.sum_le_sum hinner
    _ = ((midCut n).filter fun x => x.1 ≠ 0).card := by simp [Finset.sum_ite]
    _ = (Finset.univ.image (inIdx (n := n))).card := by
        congr 1
        ext x
        simp only [midCut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, inIdx]
        constructor
        · rintro ⟨hx0 | hxin, hne⟩
          · exact absurd hx0 hne
          · exact ⟨⟨x.1 - 2, by omega⟩, Fin.ext (by dsimp only; omega)⟩
        · rintro ⟨v, hv⟩
          subst hv
          dsimp only
          exact ⟨Or.inr ⟨by omega, by omega⟩, by omega⟩
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := Fintype.card_fin n

private theorem minSepProg_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s : Memory.State} (hG : MatrixLoaded G s) :
    let res := (Memory.spec 0).clientResult s (minSepProg (n, m))
    let t := (Memory.spec 0).clientState s (minSepProg (n, m))
    let N := splitNet G m s
    (∀ a < flowBase n, t.mem a = s.mem a) ∧
      ∃ C : Finset (Fin (splitCount n)),
        N.IsMinCut C ∧
        N.cutCapacity C ≤ n ∧
        (∀ x : Fin (splitCount n), t.mem (distBase n + x.1) < splitCount n ↔ x ∈ C) ∧
        (∀ v : Fin n, t.mem (sepOutBase n + v.1) =
          if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0) ∧
        res = (Finset.univ.filter fun v : Fin n => t.mem (sepOutBase n + v.1) = 1).card ∧
        res ≤ N.cutCapacity C := by
  intro res t N
  have hlow_all : ∀ a < flowBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_minSepProg ha s
  refine ⟨hlow_all, ?_⟩
  let M := splitCount n
  have hst_ne : N.s ≠ N.t := by
    intro h; have := congrArg Fin.val h; dsimp only [N, splitNet] at this; omega
  set s1 := (Memory.spec 0).clientState s (fillRange ((flowBase n, 0), M * M))
  have hs1 := fillRange_spec (flowBase n) 0 (M * M) s
  have hf0 : FlowStored (Network.Flow.zero N) s1 := by
    intro x y
    have hxy := hs1.1 (x.1 * M + y.1) (by dsimp only [M]; nlinarith [x.2, y.2])
    change s1.mem (flowBase n + (x.1 * M + y.1)) = 0 at hxy
    rw [← Nat.add_assoc] at hxy
    exact hxy
  have hs1_low : ∀ a < flowBase n, s1.mem a = s.mem a := fun a ha => hs1.2 a (Or.inl ha)
  have hrounds := iterate_invariant_of augRoundStep (n, m)
    (fun rem (r : ℕ) st =>
      r + rem = n ∧
      (∀ a < flowBase n, st.mem a = s.mem a) ∧
      ∃ f : N.Flow, FlowStored f st ∧ (¬ f.ResReachable N.s N.t ∨ (r : ℤ) ≤ f.value))
    (fun rem r st ⟨hrsum, hst_low, f, hf_st, hval_or⟩ => by
      unfold augRoundStep
      dsimp only
      rw [clientResult_bind, clientState_bind, clientResult_bind_read, clientState_bind_read]
      set tb := (Memory.spec 0).clientState st (bfsProg (n, m))
      obtain ⟨htb_low, htb_dist, htb_par⟩ := bfsProg_spec hG hst_low f hf_st
      have hd1_eq : tb.mem (distBase n + 1) = f.resDist N.t := htb_dist N.t
      by_cases hd1 : tb.mem (distBase n + 1) < M
      · rw [ite_eq_left hd1, cr_bind_pure, cs_bind_pure]
        have ht_reach : f.ResReachable N.s N.t := by
          rw [← f.resDist_lt_card_iff_resReachable, Fintype.card_fin]
          rwa [← hd1_eq]
        have hr_le : (r : ℤ) ≤ f.value := hval_or.resolve_left (not_not.mpr ht_reach)
        let parOf : Fin M → Fin M := fun x =>
          if h : tb.mem (parBase n + x.1) < M then ⟨tb.mem (parBase n + x.1), h⟩
          else ⟨0, by dsimp only [M, splitCount]; omega⟩
        have hparOf : ∀ x : Fin M, 0 < f.resDist x → f.resDist x < M →
            tb.mem (parBase n + x.1) = (parOf x).1 ∧
            f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x := by
          intro x hx1 hx2
          obtain ⟨u, hu1, hu2, hu3⟩ := htb_par x hx1 hx2
          have hu_lt : tb.mem (parBase n + x.1) < M := by rw [hu1]; exact u.2
          have hp_eq : parOf x = u :=
            Fin.ext (by dsimp only [parOf]; rw [dite_eq_left hu_lt]; exact hu1)
          rw [hp_eq]
          exact ⟨hu1, hu2, hu3⟩
        have hd1_lt : f.resDist N.t < M := by omega
        obtain ⟨hp_head, _, hp_nd, hp_arcs⟩ :=
          buildPath_props f parOf (fun x h1 h2 => (hparOf x h1 h2).2)
            (f.resDist N.t) N.t hd1_lt rfl
        have hp_last := buildPath_getLast? parOf (f.resDist N.t) N.t
        let f' := f.augment (buildPath parOf (f.resDist N.t) N.t) hp_nd hp_head hp_last 1 hp_arcs
        have hf_tb : FlowStored f tb := fun x y => by
          rw [htb_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf_st x y]
        have hpush := iterate_pushUnitStep_spec f parOf (fun x h1 h2 => (hparOf x h1 h2).2)
          (f.resDist N.t) N.t tb hd1_lt rfl (fun x h1 h2 => (hparOf x h1 h2).1)
          (fun x y _ => hf_tb x y)
        have hflow_f' : FlowStored f'
            ((Memory.spec 0).clientState tb (iterate pushUnitStep n (f.resDist N.t) 1)) := by
          intro x y
          change ((Memory.spec 0).clientState tb
            (iterate pushUnitStep n (f.resDist N.t) N.t.1)).mem
            (flowBase n + x.1 * splitCount n + y.1) = f' x y
          rw [hpush.2 x y, hf_tb x y]
          rfl
        rw [hd1_eq]
        refine ⟨by omega, fun a ha => (hpush.1 a ha).trans
          ((htb_low a (by dsimp only [distBase]; omega)).trans (hst_low a ha)),
          f', hflow_f', Or.inr ?_⟩
        have hval' := f.value_augment hst_ne hp_nd hp_head hp_last 1 hp_arcs
        change ((r + 1 : ℕ) : ℤ) ≤ f'.value
        rw [hval']
        omega
      · rw [ite_eq_right hd1]
        simp only [client_simps]
        have hno_reach : ¬ f.ResReachable N.s N.t := by
          rw [← f.resDist_lt_card_iff_resReachable, Fintype.card_fin, ← hd1_eq]
          exact hd1
        have hf_tb : FlowStored f tb := fun x y => by
          rw [htb_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf_st x y]
        exact ⟨by omega, fun a ha =>
          (htb_low a (by dsimp only [distBase]; omega)).trans (hst_low a ha),
          f, hf_tb, Or.inl hno_reach⟩)
    (n := n) (a := 0) (s := s1)
    ⟨Nat.zero_add _, hs1_low, Network.Flow.zero N, hf0, Or.inr (by simp)⟩
  obtain ⟨hrend, hs2_low, f_end, hf_end, hdone_or⟩ := hrounds
  set s2 := (Memory.spec 0).clientState s1 (iterate augRoundStep (n, m) n 0)
  have hr_eq_n : (Memory.spec 0).clientResult s1 (iterate augRoundStep (n, m) n 0) = n := by omega
  rw [hr_eq_n] at hdone_or
  have hno_aug : ¬ ∃ p, f_end.IsAugmentingPath p := by
    rw [f_end.exists_augmentingPath_iff_resReachable]
    rcases hdone_or with hnr | hval_ge
    · exact hnr
    · intro hreach
      obtain ⟨p, hp⟩ := f_end.exists_augmentingPath_iff_resReachable.mpr hreach
      have hlt := f_end.lt_value_augmentByBottleneck hst_ne hp
      have hle_cut := (f_end.augmentByBottleneck p hp).value_le_cutCapacity (isCut_midCut G m s)
      have hcap_mid : N.cutCapacity (midCut n) ≤ n := cutCapacity_midCut_le G m s
      change (f_end.augmentByBottleneck p hp).value ≤ (N.cutCapacity (midCut n) : ℤ) at hle_cut
      omega
  set s3 := (Memory.spec 0).clientState s2 (bfsProg (n, m))
  obtain ⟨hs3_low, hs3_dist, _⟩ := bfsProg_spec hG hs2_low f_end hf_end
  let C := f_end.reachableCut
  have hcut : N.IsCut C := f_end.reachableCut_isCut hno_aug
  have hval_cut : f_end.value = (N.cutCapacity C : ℤ) :=
    f_end.value_eq_cutCapacity_reachableCut hno_aug
  have hmin : N.IsMinCut C := f_end.isMinCut_of_value_eq_cutCapacity hcut hval_cut
  have hcapC_le : N.cutCapacity C ≤ n :=
    (hmin.2 (midCut n) (isCut_midCut G m s)).trans (cutCapacity_midCut_le G m s)
  have hdist_iff : ∀ x : Fin M, s3.mem (distBase n + x.1) < M ↔ x ∈ C := by
    intro x
    rw [hs3_dist x, f_end.mem_reachableCut_iff, ← f_end.resDist_lt_card_iff_resReachable,
      Fintype.card_fin]
  have hext := iterate_invariant_of extractSepStep n
    (fun rem (vc : ℕ × ℕ) st =>
      vc.1 + rem = n ∧
      (∀ a < sepOutBase n, st.mem a = s3.mem a) ∧
      (∀ v : Fin n, v.1 < vc.1 → st.mem (sepOutBase n + v.1) =
        if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0) ∧
      vc.2 = ((Finset.univ : Finset (Fin n)).filter fun v =>
        v.1 < vc.1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C).card)
    (fun rem vc st ⟨hvsum, hst_pre, hprev, hcnt⟩ => by
      have hv_lt : vc.1 < n := by omega
      let vFin : Fin n := ⟨vc.1, hv_lt⟩
      have hw_eq : st.mem (wBase n + vc.1) = s.mem (wBase n + vc.1) := by
        rw [hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, flowBase, wBase]; omega),
          hs3_low _ (by dsimp only [distBase, flowBase, wBase]; omega),
          hs2_low _ (by dsimp only [flowBase, wBase]; omega)]
      have hdin_eq : st.mem (distBase n + (vc.1 + 2)) = s3.mem (distBase n + (inIdx vFin).1) :=
        hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, splitCount]; omega)
      have hdout_eq : st.mem (distBase n + (vc.1 + n + 2)) =
          s3.mem (distBase n + (outIdx vFin).1) :=
        hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, splitCount]; omega)
      have hout_le : s3.mem (distBase n + (outIdx vFin).1) ≤ M := by
        rw [hs3_dist]; simpa [Fintype.card_fin] using f_end.resDist_le_card (outIdx vFin)
      have hpred_iff : (s.mem (wBase n + vc.1) = 0 ∧
          s3.mem (distBase n + (inIdx vFin).1) < M ∧
          s3.mem (distBase n + (outIdx vFin).1) = M) ↔
          (s.mem (wBase n + vc.1) = 0 ∧ inIdx vFin ∈ C ∧ outIdx vFin ∉ C) := by
        rw [← hdist_iff (inIdx vFin), ← hdist_iff (outIdx vFin)]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩,
          fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩
      unfold extractSepStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, clientResult_bind_read, clientState_bind_read,
        hw_eq, hdin_eq, hdout_eq]
      by_cases hp : s.mem (wBase n + vc.1) = 0 ∧
          s3.mem (distBase n + (inIdx vFin).1) < M ∧
          s3.mem (distBase n + (outIdx vFin).1) = M
      · have hp' := hpred_iff.mp hp
        rw [ite_eq_left hp, clientResult_bind_write, clientState_bind_write, clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hst_pre a ha
        · by_cases huv : u.1 = vc.1
          · have hueq : u = vFin := Fin.ext huv
            subst hueq
            dsimp only [vFin]
            rw [Function.update_self, ite_eq_left hp']
          · rw [Function.update_of_ne (by omega)]; exact hprev u (by omega)
        · have hfilt : ((Finset.univ : Finset (Fin n)).filter fun v =>
              v.1 < vc.1 + 1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C) =
              insert vFin (((Finset.univ : Finset (Fin n)).filter fun v =>
                v.1 < vc.1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C)) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, hw, hin, hout⟩
              by_cases hveq : v.1 = vc.1
              · exact Or.inl (Fin.ext hveq)
              · exact Or.inr ⟨by omega, hw, hin, hout⟩
            · rintro (rfl | ⟨hlt, hw, hin, hout⟩)
              · exact ⟨by dsimp only [vFin]; omega, hp'.1, hp'.2.1, hp'.2.2⟩
              · exact ⟨by omega, hw, hin, hout⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [vFin]), hcnt]
      · have hp' : ¬ (s.mem (wBase n + vc.1) = 0 ∧ inIdx vFin ∈ C ∧ outIdx vFin ∉ C) :=
          fun h => hp (hpred_iff.mpr h)
        rw [ite_eq_right hp, clientResult_bind_write, clientState_bind_write, clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hst_pre a ha
        · by_cases huv : u.1 = vc.1
          · have hueq : u = vFin := Fin.ext huv
            subst hueq
            dsimp only [vFin]
            rw [Function.update_self, ite_eq_right hp']
          · rw [Function.update_of_ne (by omega)]; exact hprev u (by omega)
        · rw [hcnt]
          symm
          congr 1
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hw, hin, hout⟩
            by_cases hveq : v.1 = vc.1
            · have hv_eq : v = vFin := Fin.ext hveq
              subst hv_eq
              exact absurd ⟨hw, hin, hout⟩ hp'
            · exact ⟨by omega, hw, hin, hout⟩
          · rintro ⟨hlt, hw, hin, hout⟩
            exact ⟨by omega, hw, hin, hout⟩)
    (n := n) (a := (0, 0)) (s := s3)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), by simp⟩
  obtain ⟨hvsum_end, hpre_end, hsep_end, hcnt_end⟩ := hext
  set s4 := (Memory.spec 0).clientState s3 (iterate extractSepStep n n (0, 0))
  set vc_end := (Memory.spec 0).clientResult s3 (iterate extractSepStep n n (0, 0))
  have hvc1 : vc_end.1 = n := by omega
  rw [hvc1] at hsep_end hcnt_end
  have hsep_fin : ∀ v : Fin n, s4.mem (sepOutBase n + v.1) =
      if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0 :=
    fun v => hsep_end v v.2
  have hcnt_fin : vc_end.2 =
      (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card := by
    rw [hcnt_end]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, v.2, hsep_fin v]
    by_cases h : s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C <;> simp [h]
  have ht_eq : t = s4 := by
    change (Memory.spec 0).clientState s (minSepProg (n, m)) = s4
    unfold minSepProg
    dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, cs_bind_pure]
  have hres_eq : res = vc_end.2 := by
    change (Memory.spec 0).clientResult s (minSepProg (n, m)) = vc_end.2
    unfold minSepProg
    dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, cr_bind_pure]
  rw [ht_eq, hres_eq]
  refine ⟨C, hmin, hcapC_le, ?_, hsep_fin, hcnt_fin, ?_⟩
  · intro x
    rw [hpre_end _ (by dsimp only [sepOutBase, parBase, distBase]; have := x.2; omega)]
    exact hdist_iff x
  · let X := Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1
    have hX_sub : X.image (inIdx (n := n)) ⊆ C := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, hsep_fin v] at hv
      split_ifs at hv with h
      exact h.2.1
    have hX_cap : ∀ v ∈ X, 1 ≤ ∑ y ∈ Finset.univ \ C, N.cap (inIdx v) y := by
      intro v hv
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, hsep_fin v] at hv
      split_ifs at hv with h
      have hout_mem : outIdx v ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.2.2⟩
      have hcap1 : N.cap (inIdx v) (outIdx v) = 1 := by
        unfold N splitNet
        dsimp only [inIdx, outIdx]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left (by omega), Nat.add_sub_cancel, ite_eq_left h.1]
      rw [← hcap1]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hout_mem
    rw [hcnt_fin]
    calc X.card
        = (X.image (inIdx (n := n))).card :=
          (Finset.card_image_of_injective X (inIdx_injective n)).symm
      _ = ∑ _x ∈ X.image (inIdx (n := n)), 1 := by simp
      _ ≤ ∑ x ∈ X.image (inIdx (n := n)), ∑ y ∈ Finset.univ \ C, N.cap x y := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
          exact hX_cap v hv
      _ ≤ ∑ x ∈ C, ∑ y ∈ Finset.univ \ C, N.cap x y :=
          Finset.sum_le_sum_of_subset hX_sub
      _ = N.cutCapacity C := rfl

/-! ### Compression leaf, base-3 odometer, and iterative compression correctness -/

private structure WListSpec {n : ℕ} (Wset : Finset (Fin n)) (L : ℕ) (s : Memory.State) : Prop where
  card_eq : L = Wset.card
  w_mem : ∀ v : Fin n, s.mem (wBase n + v.1) = if v ∈ Wset then 1 else 0
  entry_lt : ∀ j < L, s.mem (wListBase n + j) < n
  entry_mem : ∀ j : Fin L, ⟨s.mem (wListBase n + j.1), entry_lt j.1 j.2⟩ ∈ Wset
  entry_strictMono : ∀ i j, i < j → j < L → s.mem (wListBase n + i) < s.mem (wListBase n + j)
  mem_iff_exists : ∀ w : Fin n, w ∈ Wset ↔ ∃ j : Fin L, s.mem (wListBase n + j.1) = w.1

private theorem WListSpec.congr {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s₁ s₂ : Memory.State}
    (hW : WListSpec Wset L s₁)
    (heq : ∀ a, wBase n ≤ a → a < digitBase n → s₂.mem a = s₁.mem a) :
    WListSpec Wset L s₂ := by
  have hL_le : L ≤ n := by
    rw [hW.card_eq]
    exact Wset.card_le_univ.trans (by simp)
  have hw_eq : ∀ v : Fin n, s₂.mem (wBase n + v.1) = s₁.mem (wBase n + v.1) :=
    fun v => heq _ (by dsimp only [wBase]; omega) (by dsimp only [wBase, digitBase]; omega)
  have hwl_eq : ∀ j < L, s₂.mem (wListBase n + j) = s₁.mem (wListBase n + j) :=
    fun j hj => heq _ (by dsimp only [wBase, wListBase]; omega)
      (by dsimp only [wListBase, digitBase]; omega)
  refine ⟨hW.card_eq, fun v => (hw_eq v).trans (hW.w_mem v),
    fun j hj => (hwl_eq j hj).symm ▸ hW.entry_lt j hj,
    fun j => ?_,
    fun i j hij hj => by
      rw [hwl_eq i (hij.trans hj), hwl_eq j hj]
      exact hW.entry_strictMono i j hij hj,
    fun w => ?_⟩
  · have hm := hW.entry_mem j
    have he := hwl_eq j.1 j.2
    convert hm using 1
    exact Fin.ext he
  · rw [hW.mem_iff_exists]
    exact ⟨fun ⟨j, hj⟩ => ⟨j, (hwl_eq j.1 j.2).trans hj⟩,
      fun ⟨j, hj⟩ => ⟨j, (hwl_eq j.1 j.2).symm.trans hj⟩⟩

private theorem WListSpec.card_le_n {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s : Memory.State}
    (hW : WListSpec Wset L s) : L ≤ n := by
  rw [hW.card_eq]
  exact Wset.card_le_univ.trans (by simp)

private theorem WListSpec.entry_inj {n : ℕ} {Wset : Finset (Fin n)} {L : ℕ} {s : Memory.State}
    (hW : WListSpec Wset L s) {i j : Fin L}
    (h : s.mem (wListBase n + i.1) = s.mem (wListBase n + j.1)) : i = j := by
  rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (hW.entry_strictMono i.1 j.1 hlt j.2))
  · exact Fin.ext heq
  · exact absurd h.symm (ne_of_lt (hW.entry_strictMono j.1 i.1 hgt i.2))

private theorem preservesAt_buildWProg {a : ℕ} {d : ℕ × ℕ} (ha : a < wBase d.1) :
    PreservesAt a (buildWProg d) := by
  unfold buildWProg
  refine preservesAt_bind (preservesAt_copyRange (Or.inl ha)) fun _ => ?_
  refine preservesAt_bind (preservesAt_write _ (by omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate (fun vL => ?_) _ _) fun _ => preservesAt_pure _ _
  unfold buildWListStep
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  exact preservesAt_bind (preservesAt_write _ (by dsimp only [wBase, wListBase] at ha ⊢; omega))
    fun _ => preservesAt_pure _ _

private theorem buildWProg_spec {n m : ℕ} (hm : m < n) {s : Memory.State}
    (hsep01 : ∀ v : Fin n, s.mem (sepBase n + v.1) ≤ 1) :
    let S : Finset (Fin n) := Finset.univ.filter fun v => s.mem (sepBase n + v.1) = 1
    let Wset : Finset (Fin n) := insert ⟨m, hm⟩ S
    let L := (Memory.spec 0).clientResult s (buildWProg (n, m))
    let t := (Memory.spec 0).clientState s (buildWProg (n, m))
    (∀ a < wBase n, t.mem a = s.mem a) ∧ WListSpec Wset L t := by
  intro S Wset L t
  refine ⟨fun a ha => preservesAt_buildWProg ha s, ?_⟩
  set s1 := (Memory.spec 0).clientState s (copyRange ((sepBase n, wBase n), n))
  have hs1 := copyRange_spec (srcB := sepBase n) (dstB := wBase n) (len := n)
    (by dsimp only [sepBase, wBase]; omega) s
  set s2 : Memory.State := ⟨Function.update s1.mem (wBase n + m) 1, s1.frontier⟩
  have hs2_w : ∀ v : Fin n, s2.mem (wBase n + v.1) = if v ∈ Wset then 1 else 0 := by
    intro v
    dsimp only [s2]
    by_cases hvm : v.1 = m
    · have hvW : v ∈ Wset := by
        have hveq : v = ⟨m, hm⟩ := Fin.ext hvm
        subst hveq
        exact Finset.mem_insert_self _ _
      rw [hvm, Function.update_self, ite_eq_left hvW]
    · have hne_m : v ≠ ⟨m, hm⟩ := fun h => hvm (congrArg Fin.val h)
      rw [Function.update_of_ne (by omega), hs1.1 v.1 v.2]
      have hv01 := hsep01 v
      have hmemW : v ∈ Wset ↔ s.mem (sepBase n + v.1) = 1 := by
        simp [Wset, S, hne_m]
      by_cases h1 : s.mem (sepBase n + v.1) = 1
      · rw [h1, ite_eq_left (hmemW.mpr h1)]
      · rw [ite_eq_right (fun h => h1 (hmemW.mp h))]; omega
  have hiter := iterate_invariant_of buildWListStep n
    (fun rem (vL : ℕ × ℕ) st =>
      vL.1 + rem = n ∧
      (∀ a < wListBase n, st.mem a = s2.mem a) ∧
      vL.2 = (Wset.filter fun w => w.1 < vL.1).card ∧
      (∀ j < vL.2, st.mem (wListBase n + j) < vL.1 ∧
        ∃ w ∈ Wset, st.mem (wListBase n + j) = w.1) ∧
      (∀ i j, i < j → j < vL.2 → st.mem (wListBase n + i) < st.mem (wListBase n + j)) ∧
      (∀ w ∈ Wset, w.1 < vL.1 → ∃ j < vL.2, st.mem (wListBase n + j) = w.1))
    (fun rem vL st ⟨hvsum, hlow, hcard, hlt_mem, hmono, hex⟩ => by
      have hv_lt : vL.1 < n := by omega
      let vFin : Fin n := ⟨vL.1, hv_lt⟩
      have hwv : st.mem (wBase n + vL.1) = if vFin ∈ Wset then 1 else 0 :=
        (hlow _ (by dsimp only [wBase, wListBase]; omega)).trans (hs2_w vFin)
      have hL_le_v : vL.2 ≤ vL.1 := by
        rw [hcard]
        calc (Wset.filter fun w => w.1 < vL.1).card
            ≤ ((Finset.univ : Finset (Fin n)).filter fun w => w.1 < vL.1).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
          _ = ((Finset.range vL.1).attach.image
                fun x => (⟨x.1, (Finset.mem_range.mp x.2).trans hv_lt⟩ : Fin n)).card := by
              congr 1
              ext w
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
                Finset.mem_attach]
              exact ⟨fun hw => ⟨⟨w.1, Finset.mem_range.mpr hw⟩, Fin.ext rfl⟩,
                fun ⟨⟨x, hx⟩, hwx⟩ => by subst hwx; exact Finset.mem_range.mp hx⟩
          _ ≤ (Finset.range vL.1).attach.card := Finset.card_image_le
          _ = vL.1 := by simp
      unfold buildWListStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, hwv]
      by_cases hvW : vFin ∈ Wset
      · rw [ite_eq_left hvW, ite_eq_left rfl, clientResult_bind_write, clientState_bind_write,
        clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, ?_, fun j hj => ?_,
          fun i j hij hj => ?_, fun w hw hlt => ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hlow a ha
        · have hfilt : (Wset.filter fun w => w.1 < vL.1 + 1) =
              insert vFin (Wset.filter fun w => w.1 < vL.1) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hwlt⟩
              by_cases hweq : w.1 = vL.1
              · exact Or.inl (Fin.ext hweq)
              · exact Or.inr ⟨hw, by omega⟩
            · rintro (rfl | ⟨hw, hwlt⟩)
              · exact ⟨hvW, by dsimp only [vFin]; omega⟩
              · exact ⟨hw, by omega⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [vFin]), hcard]
        · by_cases hjL : j = vL.2
          · subst hjL
            rw [Function.update_self]
            exact ⟨by omega, vFin, hvW, rfl⟩
          · obtain ⟨hlt, w, hwW, hweq⟩ := hlt_mem j (by omega)
            rw [Function.update_of_ne (by omega)]
            exact ⟨by omega, w, hwW, hweq⟩
        · rw [Function.update_of_ne (by omega)]
          by_cases hjL : j = vL.2
          · subst hjL
            rw [Function.update_self]
            exact (hlt_mem i hij).1
          · rw [Function.update_of_ne (by omega)]
            exact hmono i j hij (by omega)
        · by_cases hweq : w.1 = vL.1
          · exact ⟨vL.2, by omega, by rw [Function.update_self, hweq]⟩
          · obtain ⟨j, hj, hjw⟩ := hex w hw (by omega)
            exact ⟨j, by omega, (Function.update_of_ne (by omega) _ _).trans hjw⟩
      · rw [ite_eq_right hvW, ite_eq_right (by decide : ¬ (0 = 1)), clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, hlow, ?_,
          fun j hj => ⟨(hlt_mem j hj).1.trans (by omega), (hlt_mem j hj).2⟩, hmono,
          fun w hw hlt => ?_⟩
        · rw [hcard]
          symm
          congr 1
          ext w
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hw, hwlt⟩
            refine ⟨hw, ?_⟩
            by_cases hweq : w.1 = vL.1
            · have : w = vFin := Fin.ext hweq; subst this; exact absurd hw hvW
            · omega
          · rintro ⟨hw, hwlt⟩
            exact ⟨hw, by omega⟩
        · by_cases hweq : w.1 = vL.1
          · have : w = vFin := Fin.ext hweq; subst this; exact absurd hw hvW
          · exact hex w hw (by omega))
    (n := n) (a := (0, 0)) (s := s2)
    ⟨Nat.zero_add _, fun _ _ => rfl, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hvsum_end, hlow_end, hcard_end, hlt_mem_end, hmono_end, hex_end⟩ := hiter
  set s3 := (Memory.spec 0).clientState s2 (iterate buildWListStep n n (0, 0))
  set vL_end := (Memory.spec 0).clientResult s2 (iterate buildWListStep n n (0, 0))
  have hv1 : vL_end.1 = n := by omega
  rw [hv1] at hcard_end hlt_mem_end hex_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (buildWProg (n, m)) = s3
    unfold buildWProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind_write, cs_bind_pure]
  have hL_eq : L = vL_end.2 := by
    change (Memory.spec 0).clientResult s (buildWProg (n, m)) = vL_end.2
    unfold buildWProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, clientResult_bind_write, cr_bind_pure]
  rw [ht_eq, hL_eq]
  have hfilt_univ : (Wset.filter fun w => w.1 < n) = Wset :=
    Finset.filter_eq_self.mpr fun w _ => w.2
  rw [hfilt_univ] at hcard_end
  refine ⟨hcard_end,
    fun v => (hlow_end _ (by dsimp only [wBase, wListBase]; omega)).trans (hs2_w v),
    fun j hj => (hlt_mem_end j hj).1,
    fun j => ?_,
    hmono_end,
    fun w => ⟨fun hw => ?_, fun ⟨j, hj⟩ => ?_⟩⟩
  · obtain ⟨w, hwW, hweq⟩ := (hlt_mem_end j.1 j.2).2
    have hfin : (⟨s3.mem (wListBase n + j.1), (hlt_mem_end j.1 j.2).1⟩ : Fin n) = w :=
      Fin.ext hweq
    rwa [hfin]
  · obtain ⟨j, hj, hjw⟩ := hex_end w hw w.2
    exact ⟨⟨j, hj⟩, hjw⟩
  · obtain ⟨w', hw'W, hw'eq⟩ := (hlt_mem_end j.1 j.2).2
    have hweq : w = w' := Fin.ext (hj.symm.trans hw'eq)
    rwa [hweq]

private def delSet {n : ℕ} (Wset : Finset (Fin n)) (s : Memory.State) : Finset (Fin n) :=
  Wset.filter fun w => s.mem (guessBase n + w.1) = 0

private def guessCol (n : ℕ) (s : Memory.State) (w : Fin n) : Bool :=
  s.mem (guessBase n + w.1) == 2

private theorem unpackGuessProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s) (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2) :
    let t := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
    (∀ a < guessBase n, t.mem a = s.mem a) ∧
      (∀ j : Fin L, t.mem (guessBase n + s.mem (wListBase n + j.1)) = s.mem (digitBase n + j.1)) ∧
      (∀ v : Fin n, v ∉ Wset → t.mem (guessBase n + v.1) = 0) ∧
      (∀ v : Fin n, t.mem (guessBase n + v.1) ≤ 2) := by
  intro t
  have hlow_all : ∀ a < guessBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_unpackGuessProg ha s
  refine ⟨hlow_all, ?_⟩
  set s1 := (Memory.spec 0).clientState s (fillRange ((guessBase n, 0), n))
  have hs1 := fillRange_spec (guessBase n) 0 n s
  have hiter := iterate_invariant_of unpackStep n
    (fun rem (j : ℕ) st =>
      j + rem = L ∧
      (∀ a < guessBase n, st.mem a = s.mem a) ∧
      (∀ i : Fin L, i.1 < j →
        st.mem (guessBase n + s.mem (wListBase n + i.1)) = s.mem (digitBase n + i.1)) ∧
      (∀ v : Fin n, (∀ i : Fin L, i.1 < j → s.mem (wListBase n + i.1) ≠ v.1) →
        st.mem (guessBase n + v.1) = 0) ∧
      (∀ v : Fin n, st.mem (guessBase n + v.1) ≤ 2))
    (fun rem j st ⟨hjsum, hst_low, hset, hzero, hle2⟩ => by
      have hj_lt : j < L := by omega
      let jFin : Fin L := ⟨j, hj_lt⟩
      have hL_le : L ≤ n := hW.card_le_n
      have hwv_eq : st.mem (wListBase n + j) = s.mem (wListBase n + j) :=
        hst_low _ (by dsimp only [wListBase, guessBase]; omega)
      have hdg_eq : st.mem (digitBase n + j) = s.mem (digitBase n + j) :=
        hst_low _ (by dsimp only [digitBase, guessBase]; omega)
      have hwv_lt : s.mem (wListBase n + j) < n := hW.entry_lt j hj_lt
      have hdg_le : s.mem (digitBase n + j) ≤ 2 := hdig j hj_lt
      unfold unpackStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hwv_eq, hdg_eq,
        ite_eq_left ⟨hwv_lt, hdg_le⟩, clientResult_bind_write, clientState_bind_write]
      simp only [client_simps]
      refine ⟨by omega, fun a ha => ?_, fun i hi => ?_, fun v hv => ?_, fun v => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hst_low a ha
      · by_cases hij : i.1 = j
        · rw [hij, Function.update_self]
        · have hne_w : s.mem (wListBase n + i.1) ≠ s.mem (wListBase n + j) :=
            fun h => hij (congrArg Fin.val (hW.entry_inj (j := jFin) h))
          rw [Function.update_of_ne (fun h => hne_w (by omega))]
          exact hset i (by omega)
      · have hne_j : s.mem (wListBase n + j) ≠ v.1 := hv jFin (Nat.lt_succ_self j)
        rw [Function.update_of_ne (fun h => hne_j (by omega))]
        exact hzero v fun i hi => hv i (by omega)
      · by_cases hv_eq : v.1 = s.mem (wListBase n + j)
        · rw [hv_eq, Function.update_self]; exact hdg_le
        · rw [Function.update_of_ne (by omega)]; exact hle2 v)
    (n := L) (a := 0) (s := s1)
    ⟨Nat.zero_add _, fun a ha => hs1.2 a (Or.inl ha),
      fun _ h => absurd h (Nat.not_lt_zero _),
      fun v _ => hs1.1 v.1 v.2,
      fun v => by rw [hs1.1 v.1 v.2]; decide⟩
  obtain ⟨hjsum_end, _, hset_end, hzero_end, hle2_end⟩ := hiter
  set s2 := (Memory.spec 0).clientState s1 (iterate unpackStep n L 0)
  have hj_end : (Memory.spec 0).clientResult s1 (iterate unpackStep n L 0) = L := by omega
  rw [hj_end] at hset_end hzero_end
  have ht_eq : t = s2 := by
    change (Memory.spec 0).clientState s (unpackGuessProg (n, L)) = s2
    unfold unpackGuessProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, cs_bind_pure]
  rw [ht_eq]
  refine ⟨fun j => hset_end j j.2, fun v hv => hzero_end v fun i _ h => hv ?_, hle2_end⟩
  exact (hW.mem_iff_exists v).mpr ⟨i, h⟩

private theorem checkProperProg_spec {n m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.1)) = s.mem (digitBase n + j.1))
    (hg_le : ∀ v : Fin n, s.mem (guessBase n + v.1) ≤ 2) :
    (Memory.spec 0).clientResult s (checkProperProg ((n, m), L)) =
      if ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
          u ∉ delSet Wset s → v ∉ delSet Wset s → guessCol n s u ≠ guessCol n s v
      then 1 else 0 := by
  let BadPair (i j : Fin L) : Prop :=
    let u : Fin n := ⟨s.mem (wListBase n + i.1), hW.entry_lt i.1 i.2⟩
    let v : Fin n := ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩
    0 < s.mem (digitBase n + i.1) ∧ 0 < s.mem (digitBase n + j.1) ∧
      s.mem (digitBase n + i.1) = s.mem (digitBase n + j.1) ∧ (prefixGraph G m).Adj u v
  unfold checkProperProg
  rw [clientResult_bind_read, cr_bind_pure]
  have hout := iterate_invariant_of properOuterStep ((n, m), L)
    (fun rem (iok : ℕ × ℕ) st =>
      iok.1 + rem = L ∧
      (∀ a, st.mem a = s.mem a) ∧
      iok.2 = if ∀ i j : Fin L, i.1 < iok.1 → ¬ BadPair i j then 1 else 0)
    (fun rem iok st ⟨hisum, hmem_eq, hok_eq⟩ => by
      have hi_lt : iok.1 < L := by omega
      let iFin : Fin L := ⟨iok.1, hi_lt⟩
      let uFin : Fin n := ⟨s.mem (wListBase n + iok.1), hW.entry_lt iok.1 hi_lt⟩
      unfold properOuterStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hmem_eq, hmem_eq]
      by_cases hdu : 0 < s.mem (digitBase n + iok.1)
      · rw [ite_eq_left ⟨uFin.2, hdu⟩, cr_bind_pure, cs_bind_pure]
        have hinn := iterate_invariant_of properInnerStep
          (((n, m), s.mem (wListBase n + iok.1)), s.mem (digitBase n + iok.1))
          (fun jrem (jok : ℕ × ℕ) st' =>
            jok.1 + jrem = L ∧
            (∀ a, st'.mem a = s.mem a) ∧
            jok.2 = if (∀ i j : Fin L, i.1 < iok.1 → ¬ BadPair i j) ∧
              (∀ j : Fin L, j.1 < jok.1 → ¬ BadPair iFin j) then 1 else 0)
          (fun jrem jok st' ⟨hjsum, hmem', hjok_eq⟩ => by
            have hj_lt : jok.1 < L := by omega
            let jFin : Fin L := ⟨jok.1, hj_lt⟩
            let vFin : Fin n := ⟨s.mem (wListBase n + jok.1), hW.entry_lt jok.1 hj_lt⟩
            unfold properInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
              clientState_bind_read, hmem', hmem']
            by_cases hcond : s.mem (wListBase n + iok.1) < n ∧
                s.mem (wListBase n + jok.1) < n ∧
                s.mem (wListBase n + iok.1) < m ∧
                s.mem (wListBase n + jok.1) < m ∧
                0 < s.mem (digitBase n + jok.1) ∧
                s.mem (digitBase n + iok.1) = s.mem (digitBase n + jok.1)
            · rw [ite_eq_left hcond, clientResult_bind_read, clientState_bind_read, hmem']
              have hmat := hG uFin vFin
              dsimp only [uFin, vFin] at hmat
              rw [hmat]
              by_cases hadj : G.Adj uFin vFin
              · have hbad : BadPair iFin jFin :=
                  ⟨hdu, hcond.2.2.2.2.1, hcond.2.2.2.2.2, hadj, hcond.2.2.1, hcond.2.2.2.1⟩
                have hnot_all : ¬ ((∀ i j : Fin L, i.1 < iok.1 → ¬ BadPair i j) ∧
                    (∀ j : Fin L, j.1 < jok.1 + 1 → ¬ BadPair iFin j)) :=
                  fun h => h.2 jFin (by dsimp only [jFin]; omega) hbad
                rw [ite_eq_left hadj, ite_eq_left rfl]
                simp only [client_simps]
                exact ⟨by omega, hmem', (ite_eq_right hnot_all).symm⟩
              · have hnot_bad : ¬ BadPair iFin jFin := fun hb => hadj hb.2.2.2.1
                rw [ite_eq_right hadj, ite_eq_right (by decide : ¬ (0 = 1))]
                simp only [client_simps]
                refine ⟨by omega, hmem', ?_⟩
                rw [hjok_eq]
                congr 1
                exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, fun j hj => by
                    by_cases hjeq : j.1 = jok.1
                    · have : j = jFin := Fin.ext hjeq; subst this; exact hnot_bad
                    · exact h2 j (by omega)⟩,
                  fun ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (by omega)⟩⟩
            · rw [ite_eq_right hcond]
              have hnot_bad : ¬ BadPair iFin jFin := fun hb =>
                hcond ⟨uFin.2, vFin.2, hb.2.2.2.2.1, hb.2.2.2.2.2, hb.2.1, hb.2.2.1⟩
              simp only [client_simps]
              refine ⟨by omega, hmem', ?_⟩
              rw [hjok_eq]
              congr 1
              exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, fun j hj => by
                  by_cases hjeq : j.1 = jok.1
                  · have : j = jFin := Fin.ext hjeq; subst this; exact hnot_bad
                  · exact h2 j (by omega)⟩,
                fun ⟨h1, h2⟩ => ⟨h1, fun j hj => h2 j (by omega)⟩⟩)
          (n := L) (a := (0, iok.2)) (s := st)
          ⟨Nat.zero_add _, hmem_eq, by
            rw [hok_eq]
            congr 1
            exact propext ⟨fun h => ⟨h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩, And.left⟩⟩
        obtain ⟨hjsum_end, hmem_end, hjok_end⟩ := hinn
        set res_in := (Memory.spec 0).clientResult st
          (iterate properInnerStep
            (((n, m), s.mem (wListBase n + iok.1)), s.mem (digitBase n + iok.1)) L (0, iok.2))
        have hj1 : res_in.1 = L := by omega
        rw [hj1] at hjok_end
        refine ⟨by omega, hmem_end, ?_⟩
        rw [hjok_end]
        congr 1
        exact propext ⟨fun ⟨h1, h2⟩ i j hi => by
            by_cases hieq : i.1 = iok.1
            · have : i = iFin := Fin.ext hieq; subst this; exact h2 j j.2
            · exact h1 i j (by omega),
          fun h => ⟨fun i j hi => h i j (by omega),
            fun j _ => h iFin j (by dsimp only [iFin]; omega)⟩⟩
      · have hnot_cond : ¬ (s.mem (wListBase n + iok.1) < n ∧ 0 < s.mem (digitBase n + iok.1)) :=
          fun h => hdu h.2
        rw [ite_eq_right hnot_cond]
        simp only [client_simps]
        refine ⟨by omega, hmem_eq, ?_⟩
        rw [hok_eq]
        congr 1
        exact propext ⟨fun h i j hi => by
            by_cases hieq : i.1 = iok.1
            · have : i = iFin := Fin.ext hieq; subst this; exact fun hb => hdu hb.1
            · exact h i j (by omega),
          fun h i j hi => h i j (by omega)⟩)
    (n := L) (a := (0, 1)) (s := s)
    ⟨Nat.zero_add _, fun _ => rfl, by simp⟩
  obtain ⟨hisum_end, _, hok_fin⟩ := hout
  set res_out := (Memory.spec 0).clientResult s (iterate properOuterStep ((n, m), L) L (0, 1))
  have hi1 : res_out.1 = L := by omega
  rw [hi1] at hok_fin
  rw [hok_fin]
  congr 1
  apply propext
  constructor
  · intro hno u huW v hvW hadj huD hvD hcol_eq
    obtain ⟨i, hi⟩ := (hW.mem_iff_exists u).mp huW
    obtain ⟨j, hj⟩ := (hW.mem_iff_exists v).mp hvW
    have hui : (⟨s.mem (wListBase n + i.1), hW.entry_lt i.1 i.2⟩ : Fin n) = u := Fin.ext hi
    have hvj : (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) = v := Fin.ext hj
    have hgu : s.mem (digitBase n + i.1) = s.mem (guessBase n + u.1) := by
      rw [← hg_eq i, hi]
    have hgv : s.mem (digitBase n + j.1) = s.mem (guessBase n + v.1) := by
      rw [← hg_eq j, hj]
    have hdu0 : s.mem (guessBase n + u.1) ≠ 0 := fun h =>
      huD (Finset.mem_filter.mpr ⟨huW, h⟩)
    have hdv0 : s.mem (guessBase n + v.1) ≠ 0 := fun h =>
      hvD (Finset.mem_filter.mpr ⟨hvW, h⟩)
    have hdu_le := hg_le u
    have hdv_le := hg_le v
    have hdeq : s.mem (guessBase n + u.1) = s.mem (guessBase n + v.1) := by
      unfold guessCol at hcol_eq
      rcases (by omega : s.mem (guessBase n + u.1) = 1 ∨ s.mem (guessBase n + u.1) = 2)
          with h1 | h1 <;>
        rcases (by omega : s.mem (guessBase n + v.1) = 1 ∨ s.mem (guessBase n + v.1) = 2)
          with h2 | h2 <;>
        simp [h1, h2] at hcol_eq ⊢
    exact hno i j i.2 ⟨by omega, by omega, by omega, by rwa [hui, hvj]⟩
  · intro hprop i j _ ⟨hdi, hdj, hdeq, hadj⟩
    let u : Fin n := ⟨s.mem (wListBase n + i.1), hW.entry_lt i.1 i.2⟩
    let v : Fin n := ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩
    have huW : u ∈ Wset := hW.entry_mem i
    have hvW : v ∈ Wset := hW.entry_mem j
    have hgu : s.mem (guessBase n + u.1) = s.mem (digitBase n + i.1) := hg_eq i
    have hgv : s.mem (guessBase n + v.1) = s.mem (digitBase n + j.1) := hg_eq j
    have huD : u ∉ delSet Wset s := fun h => by
      have := (Finset.mem_filter.mp h).2; omega
    have hvD : v ∉ delSet Wset s := fun h => by
      have := (Finset.mem_filter.mp h).2; omega
    exact hprop u huW v hvW hadj huD hvD (by unfold guessCol; rw [hgu, hgv, hdeq])

private theorem buildTerminalsProg_spec {n m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.1)) = s.mem (digitBase n + j.1))
    (hg_le : ∀ v : Fin n, s.mem (guessBase n + v.1) ≤ 2) :
    let t := (Memory.spec 0).clientState s (buildTerminalsProg ((n, m), L))
    let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.1) == 1
    (∀ a < keepBase n, t.mem a = s.mem a) ∧
      (∀ v : Fin n, t.mem (keepBase n + v.1) ≤ 1 ∧
        (t.mem (keepBase n + v.1) = 1 ↔
          v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
            (delSet Wset s : Set (Fin n)) (guessCol n s) c₀)) ∧
      (∀ v : Fin n, t.mem (flipBase n + v.1) ≤ 1 ∧
        (t.mem (flipBase n + v.1) = 1 ↔
          v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
            (delSet Wset s : Set (Fin n)) (guessCol n s) c₀)) := by
  intro t c₀
  have hlow_all : ∀ a < keepBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_buildTerminalsProg ha s
  refine ⟨hlow_all, ?_⟩
  set s1 := (Memory.spec 0).clientState s (fillRange ((keepBase n, 0), n))
  have hs1 := fillRange_spec (keepBase n) 0 n s
  set s2 := (Memory.spec 0).clientState s1 (fillRange ((flipBase n, 0), n))
  have hs2 := fillRange_spec (flipBase n) 0 n s1
  have hs2_low : ∀ a < keepBase n, s2.mem a = s.mem a := fun a ha =>
    (hs2.2 a (Or.inl (by dsimp only [keepBase, flipBase] at ha ⊢; omega))).trans
      (hs1.2 a (Or.inl ha))
  have hs2_keep : ∀ v : Fin n, s2.mem (keepBase n + v.1) = 0 := fun v =>
    (hs2.2 _ (Or.inl (by dsimp only [keepBase, flipBase]; omega))).trans (hs1.1 v.1 v.2)
  have hs2_flip : ∀ v : Fin n, s2.mem (flipBase n + v.1) = 0 := fun v => hs2.1 v.1 v.2
  let KeepPred (v : Fin n) : Prop :=
    v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
      (delSet Wset s : Set (Fin n)) (guessCol n s) c₀
  let FlipPred (v : Fin n) : Prop :=
    v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
      (delSet Wset s : Set (Fin n)) (guessCol n s) c₀
  have hout := iterate_invariant_of termOuterStep ((n, m), L)
    (fun rem (v : ℕ) st =>
      v + rem = n ∧
      (∀ a < keepBase n, st.mem a = s.mem a) ∧
      (∀ x : Fin n, x.1 < v →
        (st.mem (keepBase n + x.1) ≤ 1 ∧ (st.mem (keepBase n + x.1) = 1 ↔ KeepPred x)) ∧
        (st.mem (flipBase n + x.1) ≤ 1 ∧ (st.mem (flipBase n + x.1) = 1 ↔ FlipPred x))) ∧
      (∀ x : Fin n, v ≤ x.1 →
        st.mem (keepBase n + x.1) = 0 ∧ st.mem (flipBase n + x.1) = 0))
    (fun rem v st ⟨hvsum, hst_low, hdone, hzero⟩ => by
      have hv_lt : v < n := by omega
      let vFin : Fin n := ⟨v, hv_lt⟩
      have hzv_eq : st.mem (wBase n + v) = s.mem (wBase n + v) :=
        hst_low _ (by dsimp only [wBase, keepBase]; omega)
      have hcv_eq : st.mem (colBase n + v) = s.mem (colBase n + v) :=
        hst_low _ (by dsimp only [colBase, keepBase]; omega)
      have hzv_W : s.mem (wBase n + v) = 0 ↔ vFin ∉ Wset := by
        rw [hW.w_mem vFin]
        by_cases h : vFin ∈ Wset <;> simp [h]
      unfold termOuterStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, hzv_eq, hcv_eq]
      by_cases hcond : s.mem (wBase n + v) = 0 ∧ v < m
      · rw [ite_eq_left hcond, cr_bind_pure, cs_bind_pure]
        have hv_notW : vFin ∉ Wset := hzv_W.mp hcond.1
        let KeepBefore (j : ℕ) : Prop :=
          ∃ idx : Fin L, idx.1 < j ∧
            let u : Fin n := ⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩
            0 < s.mem (digitBase n + idx.1) ∧ (prefixGraph G m).Adj u vFin ∧
              guessCol n s u ≠ c₀ vFin
        let FlipBefore (j : ℕ) : Prop :=
          ∃ idx : Fin L, idx.1 < j ∧
            let u : Fin n := ⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩
            0 < s.mem (digitBase n + idx.1) ∧ (prefixGraph G m).Adj u vFin ∧
              guessCol n s u = c₀ vFin
        have hinn := iterate_invariant_of termInnerStep ((n, m), (v, s.mem (colBase n + v)))
          (fun jrem (j : ℕ) st' =>
            j + jrem = L ∧
            (∀ a < keepBase n, st'.mem a = s.mem a) ∧
            (∀ x : Fin n, x ≠ vFin →
              st'.mem (keepBase n + x.1) = st.mem (keepBase n + x.1) ∧
              st'.mem (flipBase n + x.1) = st.mem (flipBase n + x.1)) ∧
            (st'.mem (keepBase n + v) ≤ 1 ∧ (st'.mem (keepBase n + v) = 1 ↔ KeepBefore j)) ∧
            (st'.mem (flipBase n + v) ≤ 1 ∧ (st'.mem (flipBase n + v) = 1 ↔ FlipBefore j)))
          (fun jrem j st' ⟨hjsum, hi_low, hi_other, hi_keep, hi_flip⟩ => by
            have hj_lt : j < L := by omega
            let jFin : Fin L := ⟨j, hj_lt⟩
            let uFin : Fin n := ⟨s.mem (wListBase n + j), hW.entry_lt j hj_lt⟩
            unfold termInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
              clientState_bind_read,
              hi_low _ (by dsimp only [wListBase, keepBase]; have := hW.card_le_n; omega),
              hi_low _ (by dsimp only [digitBase, keepBase]; have := hW.card_le_n; omega)]
            by_cases hicond : s.mem (wListBase n + j) < n ∧ v < n ∧
                s.mem (wListBase n + j) < m ∧ v < m ∧ 0 < s.mem (digitBase n + j)
            · rw [ite_eq_left hicond, clientResult_bind_read, clientState_bind_read,
                hi_low _ (by dsimp only [keepBase]; nlinarith [uFin.2, vFin.2])]
              have hmat := hG uFin vFin
              dsimp only [uFin, vFin] at hmat
              rw [hmat]
              by_cases hadj : G.Adj uFin vFin
              · have hp_adj : (prefixGraph G m).Adj uFin vFin :=
                  ⟨hadj, hicond.2.2.1, hicond.2.2.2.1⟩
                rw [ite_eq_left hadj, ite_eq_left rfl]
                have hgu : s.mem (guessBase n + uFin.1) = s.mem (digitBase n + j) := hg_eq jFin
                have hdu_le : s.mem (digitBase n + j) ≤ 2 := hgu ▸ hg_le uFin
                have hcv_le : s.mem (colBase n + v) ≤ 1 := hcol01 vFin
                have hcol_iff : s.mem (digitBase n + j) - 1 = s.mem (colBase n + v) ↔
                    guessCol n s uFin = c₀ vFin := by
                  unfold guessCol c₀
                  dsimp only [vFin]
                  rw [hgu]
                  have hdpos := hicond.2.2.2.2
                  rcases (by omega : s.mem (digitBase n + j) = 1 ∨ s.mem (digitBase n + j) = 2)
                      with hd | hd <;>
                    rcases (by omega : s.mem (colBase n + v) = 0 ∨ s.mem (colBase n + v) = 1)
                      with hc | hc <;>
                    simp [hd, hc]
                by_cases hsame : s.mem (digitBase n + j) - 1 = s.mem (colBase n + v)
                · have hsame' := hcol_iff.mp hsame
                  rw [ite_eq_left hsame, clientResult_bind_write, clientState_bind_write]
                  simp only [client_simps]
                  have hflip_succ : FlipBefore (j + 1) :=
                    ⟨jFin, by dsimp only [jFin]; omega, hicond.2.2.2.2, hp_adj, hsame'⟩
                  have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                    ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                        by_cases heq : idx.1 = j
                        · have : idx = jFin := Fin.ext heq; subst this; exact absurd hsame' h3
                        · exact ⟨idx, by omega, h1, h2, h3⟩,
                      fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                  refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, ?_, ?_⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase] at ha ⊢; omega)]
                    exact hi_low a ha
                  · have hxv : x.1 ≠ v := fun h => hx (Fin.ext h)
                    exact ⟨(Function.update_of_ne
                        (by dsimp only [keepBase, flipBase]; omega) _ _).trans (hi_other x hx).1,
                      (Function.update_of_ne (by omega) _ _).trans (hi_other x hx).2⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase]; omega),
                      hkeep_iff]
                    exact hi_keep
                  · rw [Function.update_self]
                    exact ⟨le_rfl, ⟨fun _ => hflip_succ, fun _ => rfl⟩⟩
                · have hdiff : guessCol n s uFin ≠ c₀ vFin := fun h => hsame (hcol_iff.mpr h)
                  rw [ite_eq_right hsame, clientResult_bind_write, clientState_bind_write]
                  simp only [client_simps]
                  have hkeep_succ : KeepBefore (j + 1) :=
                    ⟨jFin, by dsimp only [jFin]; omega, hicond.2.2.2.2, hp_adj, hdiff⟩
                  have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                    ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                        by_cases heq : idx.1 = j
                        · have : idx = jFin := Fin.ext heq; subst this; exact absurd h3 hdiff
                        · exact ⟨idx, by omega, h1, h2, h3⟩,
                      fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                  refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, ?_, ?_⟩
                  · rw [Function.update_of_ne (by omega)]; exact hi_low a ha
                  · have hxv : x.1 ≠ v := fun h => hx (Fin.ext h)
                    exact ⟨(Function.update_of_ne (by omega) _ _).trans (hi_other x hx).1,
                      (Function.update_of_ne
                        (by dsimp only [keepBase, flipBase]; omega) _ _).trans (hi_other x hx).2⟩
                  · rw [Function.update_self]
                    exact ⟨le_rfl, ⟨fun _ => hkeep_succ, fun _ => rfl⟩⟩
                  · rw [Function.update_of_ne (by dsimp only [keepBase, flipBase]; omega),
                      hflip_iff]
                    exact hi_flip
              · rw [ite_eq_right hadj, ite_eq_right (by decide : ¬ (0 = 1))]
                simp only [client_simps]
                have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                  ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                      by_cases heq : idx.1 = j
                      · have : idx = jFin := Fin.ext heq; subst this; exact absurd h2.1 hadj
                      · exact ⟨idx, by omega, h1, h2, h3⟩,
                    fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                  ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                      by_cases heq : idx.1 = j
                      · have : idx = jFin := Fin.ext heq; subst this; exact absurd h2.1 hadj
                      · exact ⟨idx, by omega, h1, h2, h3⟩,
                    fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
                refine ⟨by omega, hi_low, hi_other, ?_, ?_⟩
                · rw [hkeep_iff]; exact hi_keep
                · rw [hflip_iff]; exact hi_flip
            · rw [ite_eq_right hicond]
              simp only [client_simps]
              have hno_j : ¬ (0 < s.mem (digitBase n + j) ∧ (prefixGraph G m).Adj uFin vFin) :=
                fun ⟨hpos, hadj⟩ => hicond ⟨uFin.2, hv_lt, hadj.2.1, hadj.2.2, hpos⟩
              have hkeep_iff : KeepBefore (j + 1) ↔ KeepBefore j :=
                ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                    by_cases heq : idx.1 = j
                    · have : idx = jFin := Fin.ext heq; subst this; exact absurd ⟨h1, h2⟩ hno_j
                    · exact ⟨idx, by omega, h1, h2, h3⟩,
                  fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
              have hflip_iff : FlipBefore (j + 1) ↔ FlipBefore j :=
                ⟨fun ⟨idx, hidx, h1, h2, h3⟩ => by
                    by_cases heq : idx.1 = j
                    · have : idx = jFin := Fin.ext heq; subst this; exact absurd ⟨h1, h2⟩ hno_j
                    · exact ⟨idx, by omega, h1, h2, h3⟩,
                  fun ⟨idx, hidx, h1, h2, h3⟩ => ⟨idx, by omega, h1, h2, h3⟩⟩
              refine ⟨by omega, hi_low, hi_other, ?_, ?_⟩
              · rw [hkeep_iff]; exact hi_keep
              · rw [hflip_iff]; exact hi_flip)
          (n := L) (a := 0) (s := st)
          ⟨Nat.zero_add _, hst_low, fun _ _ => ⟨rfl, rfl⟩,
            by
              rw [(hzero vFin le_rfl).1]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide),
                fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩⟩,
            by
              rw [(hzero vFin le_rfl).2]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide),
                fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩⟩⟩
        obtain ⟨hjsum_end, hi_low_end, hi_other_end, hi_keep_end, hi_flip_end⟩ := hinn
        have hj_end : (Memory.spec 0).clientResult st
            (iterate termInnerStep ((n, m), (v, s.mem (colBase n + v))) L 0) = L := by omega
        rw [hj_end] at hi_keep_end hi_flip_end
        have hkeep_eq : KeepBefore L ↔ KeepPred vFin := by
          dsimp only [KeepPred]
          rw [mem_keepTerminals]
          constructor
          · rintro ⟨idx, _, hpos, hadj, hne⟩
            let u : Fin n := ⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩
            have huW : u ∈ Wset := hW.entry_mem idx
            have huD : u ∉ delSet Wset s := fun h => by
              have h0 : s.mem (guessBase n + s.mem (wListBase n + idx.1)) = 0 :=
                (Finset.mem_filter.mp h).2
              rw [hg_eq idx] at h0
              omega
            exact ⟨hv_notW, u, huW, huD, hadj, hne⟩
          · rintro ⟨_, u, huW, huD, hadj, hne⟩
            obtain ⟨idx, hidx⟩ := (hW.mem_iff_exists u).mp huW
            have hui : (⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩ : Fin n) = u :=
              Fin.ext hidx
            have hgu := hg_eq idx
            have hpos : 0 < s.mem (digitBase n + idx.1) := by
              rw [← hgu, hidx]
              have : s.mem (guessBase n + u.1) ≠ 0 := fun h =>
                huD (Finset.mem_filter.mpr ⟨huW, h⟩)
              omega
            exact ⟨idx, idx.2, hpos, by rwa [hui], by rwa [hui]⟩
        have hflip_eq : FlipBefore L ↔ FlipPred vFin := by
          dsimp only [FlipPred]
          rw [mem_flipTerminals]
          constructor
          · rintro ⟨idx, _, hpos, hadj, heq⟩
            let u : Fin n := ⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩
            have huW : u ∈ Wset := hW.entry_mem idx
            have huD : u ∉ delSet Wset s := fun h => by
              have h0 : s.mem (guessBase n + s.mem (wListBase n + idx.1)) = 0 :=
                (Finset.mem_filter.mp h).2
              rw [hg_eq idx] at h0
              omega
            exact ⟨hv_notW, u, huW, huD, hadj, heq⟩
          · rintro ⟨_, u, huW, huD, hadj, heq⟩
            obtain ⟨idx, hidx⟩ := (hW.mem_iff_exists u).mp huW
            have hui : (⟨s.mem (wListBase n + idx.1), hW.entry_lt idx.1 idx.2⟩ : Fin n) = u :=
              Fin.ext hidx
            have hgu := hg_eq idx
            have hpos : 0 < s.mem (digitBase n + idx.1) := by
              rw [← hgu, hidx]
              have : s.mem (guessBase n + u.1) ≠ 0 := fun h =>
                huD (Finset.mem_filter.mpr ⟨huW, h⟩)
              omega
            exact ⟨idx, idx.2, hpos, by rwa [hui], by rwa [hui]⟩
        refine ⟨by omega, hi_low_end, fun x hx => ?_, fun x hx => ?_⟩
        · by_cases hxv : x.1 = v
          · have hxeq : x = vFin := Fin.ext hxv
            subst hxeq
            exact ⟨⟨hi_keep_end.1, hi_keep_end.2.trans hkeep_eq⟩,
              ⟨hi_flip_end.1, hi_flip_end.2.trans hflip_eq⟩⟩
          · have hne : x ≠ vFin := fun h => hxv (congrArg Fin.val h)
            obtain ⟨⟨hk_le, hk_iff⟩, ⟨hf_le, hf_iff⟩⟩ := hdone x (by omega)
            obtain ⟨hk_eq, hf_eq⟩ := hi_other_end x hne
            exact ⟨⟨hk_eq.trans_le hk_le, by rw [hk_eq]; exact hk_iff⟩,
              ⟨hf_eq.trans_le hf_le, by rw [hf_eq]; exact hf_iff⟩⟩
        · have hne : x ≠ vFin := fun h => by subst h; dsimp only [vFin] at hx; omega
          exact ⟨(hi_other_end x hne).1.trans (hzero x (by omega)).1,
            (hi_other_end x hne).2.trans (hzero x (by omega)).2⟩
      · rw [ite_eq_right hcond]
        simp only [client_simps]
        have hno_keep : ¬ KeepPred vFin := fun h => by
          obtain ⟨hnW, u, _, _, hadj, _⟩ := mem_keepTerminals.mp h
          exact hcond ⟨hzv_W.mpr hnW, hadj.2.2⟩
        have hno_flip : ¬ FlipPred vFin := fun h => by
          obtain ⟨hnW, u, _, _, hadj, _⟩ := mem_flipTerminals.mp h
          exact hcond ⟨hzv_W.mpr hnW, hadj.2.2⟩
        refine ⟨by omega, hst_low, fun x hx => ?_, fun x hx => hzero x (by omega)⟩
        by_cases hxv : x.1 = v
        · have hxeq : x = vFin := Fin.ext hxv
          subst hxeq
          exact ⟨by
              rw [(hzero vFin le_rfl).1]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide), fun h => absurd h hno_keep⟩⟩,
            by
              rw [(hzero vFin le_rfl).2]
              exact ⟨Nat.zero_le 1, ⟨fun h => absurd h (by decide), fun h => absurd h hno_flip⟩⟩⟩
        · exact hdone x (by omega))
    (n := n) (a := 0) (s := s2)
    ⟨Nat.zero_add _, hs2_low, fun _ h => absurd h (Nat.not_lt_zero _),
      fun x _ => ⟨hs2_keep x, hs2_flip x⟩⟩
  obtain ⟨hvsum_end, _, hdone_end, _⟩ := hout
  set s3 := (Memory.spec 0).clientState s2 (iterate termOuterStep ((n, m), L) n 0)
  have hv_end : (Memory.spec 0).clientResult s2 (iterate termOuterStep ((n, m), L) n 0) = n := by
    omega
  rw [hv_end] at hdone_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (buildTerminalsProg ((n, m), L)) = s3
    unfold buildTerminalsProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, cs_bind_pure]
  rw [ht_eq]
  exact ⟨fun v => (hdone_end v v.2).1, fun v => (hdone_end v v.2).2⟩

private theorem countDelProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s)
    (hg_eq : ∀ j : Fin L,
      s.mem (guessBase n + s.mem (wListBase n + j.1)) = s.mem (digitBase n + j.1)) :
    (Memory.spec 0).clientResult s (countDelProg (n, L)) = (delSet Wset s).card := by
  unfold countDelProg
  rw [clientResult_bind_read, cr_bind_pure]
  have hiter := iterate_invariant_of countDelStep n
    (fun rem (jc : ℕ × ℕ) st =>
      jc.1 + rem = L ∧
      (∀ a, st.mem a = s.mem a) ∧
      jc.2 = ((Finset.univ : Finset (Fin L)).filter fun j =>
        j.1 < jc.1 ∧ s.mem (digitBase n + j.1) = 0).card)
    (fun rem jc st ⟨hjsum, hmem_eq, hcnt⟩ => by
      have hj_lt : jc.1 < L := by omega
      let jFin : Fin L := ⟨jc.1, hj_lt⟩
      unfold countDelStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, hmem_eq]
      by_cases h0 : s.mem (digitBase n + jc.1) = 0
      · rw [ite_eq_left h0, clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, hmem_eq, ?_⟩
        have hfilt : ((Finset.univ : Finset (Fin L)).filter fun j =>
            j.1 < jc.1 + 1 ∧ s.mem (digitBase n + j.1) = 0) =
            insert jFin (((Finset.univ : Finset (Fin L)).filter fun j =>
              j.1 < jc.1 ∧ s.mem (digitBase n + j.1) = 0)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          exact ⟨fun ⟨hlt, hd⟩ => by
              by_cases hjeq : j.1 = jc.1
              · exact Or.inl (Fin.ext hjeq)
              · exact Or.inr ⟨by omega, hd⟩,
            fun h => h.elim (fun h => by subst h; exact ⟨by dsimp only [jFin]; omega, h0⟩)
              fun ⟨hlt, hd⟩ => ⟨by omega, hd⟩⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp [jFin]), hcnt]
      · rw [ite_eq_right h0, clientResult_pure, clientState_pure]
        dsimp only
        refine ⟨by omega, hmem_eq, ?_⟩
        rw [hcnt]
        symm
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨hlt, hd⟩ => by
            by_cases hjeq : j.1 = jc.1
            · exact absurd (hjeq ▸ hd) h0
            · exact ⟨by omega, hd⟩,
          fun ⟨hlt, hd⟩ => ⟨by omega, hd⟩⟩)
    (n := L) (a := (0, 0)) (s := s)
    ⟨Nat.zero_add _, fun _ => rfl, by simp⟩
  obtain ⟨hjsum_end, _, hcnt_end⟩ := hiter
  set jc_end := (Memory.spec 0).clientResult s (iterate countDelStep n L (0, 0))
  have hj1 : jc_end.1 = L := by omega
  rw [hj1] at hcnt_end
  rw [hcnt_end]
  let fEmb : Fin L → Fin n := fun j => ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩
  have hf_inj : Function.Injective fEmb := fun i j h => hW.entry_inj (congrArg Fin.val h)
  have himg : ((Finset.univ : Finset (Fin L)).filter fun j =>
      j.1 < L ∧ s.mem (digitBase n + j.1) = 0).image fEmb = delSet Wset s := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, delSet]
    constructor
    · rintro ⟨j, ⟨_, hd0⟩, rfl⟩
      exact ⟨hW.entry_mem j, (hg_eq j).trans hd0⟩
    · rintro ⟨hwW, hg0⟩
      obtain ⟨j, hj⟩ := (hW.mem_iff_exists w).mp hwW
      exact ⟨j, ⟨j.2, (hg_eq j).symm.trans (hj.symm ▸ hg0)⟩, Fin.ext hj⟩
  rw [← himg, Finset.card_image_of_injective _ hf_inj]

private theorem commitLeafProg_spec {n L : ℕ} {Wset : Finset (Fin n)} {s : Memory.State}
    (hW : WListSpec Wset L s)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1) :
    let t := (Memory.spec 0).clientState s (commitLeafProg n)
    let X : Finset (Fin n) := Finset.univ.filter fun v => s.mem (sepOutBase n + v.1) = 1
    (∀ a, (a < sepBase n ∨ wBase n ≤ a) → t.mem a = s.mem a) ∧
      (∀ v : Fin n, t.mem (sepBase n + v.1) = if v ∈ delSet Wset s ∪ X then 1 else 0) ∧
      (∀ v : Fin n, t.mem (colBase n + v.1) ≤ 1) ∧
      (∀ v ∈ Wset, (t.mem (colBase n + v.1) == 1) = guessCol n s v) ∧
      (∀ v : Fin n, v ∉ Wset →
        (t.mem (colBase n + v.1) == 1) =
          ((s.mem (colBase n + v.1) == 1) ==
            decide (s.mem (distBase n + (outIdx v).1) < splitCount n))) := by
  intro t X
  have hpres : ∀ a, (a < sepBase n ∨ wBase n ≤ a) → t.mem a = s.mem a :=
    fun a ha => preservesAt_commitLeafProg ha s
  refine ⟨hpres, ?_⟩
  let NewCol (v : Fin n) : ℕ :=
    if v ∈ Wset then
      if s.mem (guessBase n + v.1) = 2 then 1 else 0
    else if s.mem (distBase n + (outIdx v).1) < splitCount n then
      if s.mem (colBase n + v.1) = 1 then 1 else 0
    else
      if s.mem (colBase n + v.1) = 1 then 0 else 1
  have hiter := iterate_invariant_of commitStep n
    (fun rem (v : ℕ) st =>
      v + rem = n ∧
      (∀ a, (a < sepBase n ∨ wBase n ≤ a) → st.mem a = s.mem a) ∧
      (∀ u : Fin n, v ≤ u.1 → st.mem (colBase n + u.1) = s.mem (colBase n + u.1)) ∧
      (∀ u : Fin n, u.1 < v →
        st.mem (sepBase n + u.1) = (if u ∈ delSet Wset s ∪ X then 1 else 0) ∧
        st.mem (colBase n + u.1) = NewCol u))
    (fun rem v st ⟨hvsum, hst_out, hcol_ge, hdone⟩ => by
      have hv_lt : v < n := by omega
      let vFin : Fin n := ⟨v, hv_lt⟩
      have hwv : st.mem (wBase n + v) = s.mem (wBase n + v) :=
        hst_out _ (Or.inr (Nat.le_add_right _ _))
      have hgv : st.mem (guessBase n + v) = s.mem (guessBase n + v) :=
        hst_out _ (Or.inr (by dsimp only [wBase, guessBase]; omega))
      have hxv : st.mem (sepOutBase n + v) = s.mem (sepOutBase n + v) :=
        hst_out _ (Or.inr (by dsimp only [wBase, sepOutBase, parBase, distBase, flowBase]; omega))
      have hcv : st.mem (colBase n + v) = s.mem (colBase n + v) := hcol_ge vFin le_rfl
      have hdout : st.mem (distBase n + (v + n + 2)) = s.mem (distBase n + (outIdx vFin).1) :=
        hst_out _ (Or.inr (by dsimp only [wBase, distBase, flowBase]; omega))
      have hw_iff : s.mem (wBase n + v) = 1 ↔ vFin ∈ Wset := by
        rw [hW.w_mem vFin]; by_cases h : vFin ∈ Wset <;> simp [h]
      have hmem_UX : ((s.mem (wBase n + v) = 1 ∧ s.mem (guessBase n + v) = 0) ∨
          s.mem (sepOutBase n + v) = 1) ↔ vFin ∈ delSet Wset s ∪ X := by
        rw [Finset.mem_union, delSet, Finset.mem_filter, Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, hw_iff]
        rfl
      let sepVal : ℕ := if vFin ∈ delSet Wset s ∪ X then 1 else 0
      have hstep1 :
          (Memory.spec 0).clientState st (commitStep (n, v)) =
            ⟨Function.update (Function.update st.mem (sepBase n + v) sepVal)
              (colBase n + v) (NewCol vFin), st.frontier⟩ ∧
          (Memory.spec 0).clientResult st (commitStep (n, v)) = v + 1 := by
        unfold commitStep
        dsimp only [sepVal, NewCol]
        rw [clientState_bind_read, clientResult_bind_read, clientState_bind_read,
          clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
          clientState_bind_read, clientResult_bind_read, clientState_bind_read,
            clientResult_bind_read, hwv, hgv, hxv, hcv, hdout]
        by_cases hux : (s.mem (wBase n + v) = 1 ∧ s.mem (guessBase n + v) = 0) ∨
            s.mem (sepOutBase n + v) = 1 <;>
          by_cases hw1 : s.mem (wBase n + v) = 1
        · rw [ite_eq_left hux, ite_eq_left (hmem_UX.mp hux), clientState_bind_write,
          clientResult_bind_write,
            ite_eq_left hw1, ite_eq_left (hw_iff.mp hw1)]
          by_cases hg2 : s.mem (guessBase n + v) = 2
          · rw [ite_eq_left hg2, ite_eq_left hg2, clientState_bind_write, clientResult_bind_write]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hg2, ite_eq_right hg2, clientState_bind_write,
            clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_left hux, ite_eq_left (hmem_UX.mp hux), clientState_bind_write,
          clientResult_bind_write,
            ite_eq_right hw1, ite_eq_right (fun h => hw1 (hw_iff.mpr h))]
          by_cases hd : s.mem (distBase n + (outIdx vFin).1) < splitCount n <;>
            by_cases hc1 : s.mem (colBase n + v) = 1
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hux, ite_eq_right (fun h => hux (hmem_UX.mpr h)),
            clientState_bind_write, clientResult_bind_write, ite_eq_left hw1,
              ite_eq_left (hw_iff.mp hw1)]
          by_cases hg2 : s.mem (guessBase n + v) = 2
          · rw [ite_eq_left hg2, ite_eq_left hg2, clientState_bind_write, clientResult_bind_write]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hg2, ite_eq_right hg2, clientState_bind_write,
            clientResult_bind_write]; exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hux, ite_eq_right (fun h => hux (hmem_UX.mpr h)),
            clientState_bind_write, clientResult_bind_write, ite_eq_right hw1,
            ite_eq_right (fun h => hw1 (hw_iff.mpr h))]
          by_cases hd : s.mem (distBase n + (outIdx vFin).1) < splitCount n <;>
            by_cases hc1 : s.mem (colBase n + v) = 1
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_left hc1, ite_eq_left hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hd, ite_eq_right hd, ite_eq_right hc1, ite_eq_right hc1,
              clientState_bind_write, clientResult_bind_write]; exact ⟨rfl, rfl⟩
      rw [hstep1.1, hstep1.2]
      dsimp only
      refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, fun u hu => ?_⟩
      · rw [Function.update_of_ne (by dsimp only [sepBase, colBase, wBase] at ha ⊢; omega),
          Function.update_of_ne (by dsimp only [sepBase, wBase] at ha ⊢; omega)]
        exact hst_out a ha
      · rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by dsimp only [sepBase, colBase]; omega)]
        exact hcol_ge u (by omega)
      · by_cases huv : u.1 = v
        · have hueq : u = vFin := Fin.ext huv
          subst hueq
          dsimp only [vFin]
          exact ⟨by rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              Function.update_self],
            by rw [Function.update_self]⟩
        · refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; have := u.2; omega),
              Function.update_of_ne (by omega)]
            exact (hdone u (by omega)).1
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [sepBase, colBase]; have := u.2; omega)]
            exact (hdone u (by omega)).2)
    (n := n) (a := 0) (s := s)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hvsum_end, _, _, hdone_end⟩ := hiter
  set s1 := (Memory.spec 0).clientState s (iterate commitStep n n 0)
  have hv_end : (Memory.spec 0).clientResult s (iterate commitStep n n 0) = n := by omega
  rw [hv_end] at hdone_end
  have ht_eq : t = s1 := by
    change (Memory.spec 0).clientState s (commitLeafProg n) = s1
    unfold commitLeafProg
    rw [clientState_bind_read, cs_bind_pure]
  rw [ht_eq]
  refine ⟨fun v => (hdone_end v v.2).1, fun v => ?_, fun v hvW => ?_, fun v hvW => ?_⟩
  · rw [(hdone_end v v.2).2]
    dsimp only [NewCol]
    split_ifs <;> decide
  · rw [(hdone_end v v.2).2]
    dsimp only [NewCol]
    rw [ite_eq_left hvW]
    unfold guessCol
    by_cases h : s.mem (guessBase n + v.1) = 2 <;> simp [h]
  · rw [(hdone_end v v.2).2]
    dsimp only [NewCol]
    rw [ite_eq_right hvW]
    have hc_le := hcol01 v
    by_cases hd : s.mem (distBase n + (outIdx v).1) < splitCount n <;>
      rcases (by omega : s.mem (colBase n + v.1) = 0 ∨ s.mem (colBase n + v.1) = 1) with hc | hc <;>
      simp [hd, hc]

private def OctStateAt {n : ℕ} (G : SimpleGraph (Fin n)) (m k : ℕ) (t : Memory.State) : Prop :=
  (∀ v : Fin n, t.mem (sepBase n + v.1) ≤ 1 ∧ t.mem (colBase n + v.1) ≤ 1) ∧
    let S := Finset.univ.filter fun v : Fin n => t.mem (sepBase n + v.1) = 1
    S.card ≤ k ∧
      ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ S → v ∉ S →
        (t.mem (colBase n + u.1) == 1) ≠ (t.mem (colBase n + v.1) == 1)

private theorem OctStateAt.congr {n : ℕ} {G : SimpleGraph (Fin n)} {m k : ℕ}
    {s₁ s₂ : Memory.State} (h : OctStateAt G m k s₁)
    (heq : ∀ a, sepBase n ≤ a → a < wBase n → s₂.mem a = s₁.mem a) :
    OctStateAt G m k s₂ := by
  have hsep : ∀ v : Fin n, s₂.mem (sepBase n + v.1) = s₁.mem (sepBase n + v.1) :=
    fun v => heq _ (by omega) (by dsimp only [sepBase, wBase]; omega)
  have hcol : ∀ v : Fin n, s₂.mem (colBase n + v.1) = s₁.mem (colBase n + v.1) :=
    fun v => heq _ (by dsimp only [sepBase, colBase]; omega) (by dsimp only [colBase, wBase]; omega)
  have hS : (Finset.univ.filter fun v : Fin n => s₂.mem (sepBase n + v.1) = 1) =
      (Finset.univ.filter fun v : Fin n => s₁.mem (sepBase n + v.1) = 1) := by
    ext v; simp [hsep v]
  refine ⟨fun v => ⟨(hsep v).trans_le (h.1 v).1, (hcol v).trans_le (h.1 v).2⟩, ?_⟩
  dsimp only
  rw [hS]
  refine ⟨h.2.1, fun u v hadj hu hv => ?_⟩
  rw [hcol u, hcol v]
  exact h.2.2 u v hadj hu hv

private theorem cap_lt_succ_of_cutCapacity_le {n : ℕ} {N : Network (Fin (splitCount n))}
    {C : Finset (Fin (splitCount n))} (hcap : N.cutCapacity C ≤ n)
    {x y : Fin (splitCount n)} (hx : x ∈ C) (hy : y ∉ C) :
    N.cap x y < n + 1 := by
  have hy' : y ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
  have h1 : N.cap x y ≤ ∑ z ∈ Finset.univ \ C, N.cap x z :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy'
  have h2 : ∑ z ∈ Finset.univ \ C, N.cap x z ≤ N.cutCapacity C := by
    unfold Network.cutCapacity
    exact Finset.single_le_sum (f := fun u => ∑ z ∈ Finset.univ \ C, N.cap u z)
      (fun _ _ => Nat.zero_le _) hx
  omega

private theorem leafProg_spec {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1)) :
    let res := (Memory.spec 0).clientResult s (leafProg (((n, k), m), L))
    let t := (Memory.spec 0).clientState s (leafProg (((n, k), m), L))
    res ≤ 1 ∧
      (∀ a, (a < sepBase n ∨ (wBase n ≤ a ∧ a < guessBase n)) → t.mem a = s.mem a) ∧
      (res = 0 → ∀ a < guessBase n, t.mem a = s.mem a) ∧
      (res = 1 → OctStateAt G m k t) := by
  intro res t
  have hpres_base : ∀ a, (a < sepBase n ∨ (wBase n ≤ a ∧ a < guessBase n)) → t.mem a = s.mem a :=
    fun a ha => preservesAt_leafProg ha s
  set s1 := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
  obtain ⟨hs1_low, hg_eq, _, hg_le⟩ := unpackGuessProg_spec hW hdig
  have hG1 : MatrixLoaded G s1 := fun u v =>
    (hs1_low _ (by dsimp only [guessBase]; nlinarith [u.2, v.2])).trans (hG u v)
  have hW1 : WListSpec Wset L s1 :=
    hW.congr fun a _ ha => hs1_low a (by dsimp only [digitBase, guessBase] at ha ⊢; omega)
  have hg_eq1 : ∀ j : Fin L,
      s1.mem (guessBase n + s1.mem (wListBase n + j.1)) = s1.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs1_low (wListBase n + j.1) (by dsimp only [wListBase, guessBase]; omega),
      hs1_low (digitBase n + j.1) (by dsimp only [digitBase, guessBase]; omega)]
    exact hg_eq j
  have hcol01_1 : ∀ v : Fin n, s1.mem (colBase n + v.1) ≤ 1 := fun v =>
    (hs1_low _ (by dsimp only [colBase, guessBase]; omega)).trans_le (hcol01 v)
  have hchk := checkProperProg_spec (m := m) hG1 hW1 hg_eq1 hg_le
  set s2 := (Memory.spec 0).clientState s1 (checkProperProg ((n, m), L))
  have hs2_eq : ∀ a, s2.mem a = s1.mem a := fun a => preservesAt_checkProperProg a _ s1
  by_cases hprop : ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
      u ∉ delSet Wset s1 → v ∉ delSet Wset s1 → guessCol n s1 u ≠ guessCol n s1 v
  · have hok1 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 1 := by
      rw [hchk, ite_eq_left hprop]
    have hG2 : MatrixLoaded G s2 := fun u v => (hs2_eq _).trans (hG1 u v)
    have hW2 : WListSpec Wset L s2 := hW1.congr fun a _ _ => hs2_eq a
    have hcol01_2 : ∀ v : Fin n, s2.mem (colBase n + v.1) ≤ 1 :=
      fun v => (hs2_eq _).trans_le (hcol01_1 v)
    have hg_eq2 : ∀ j : Fin L,
        s2.mem (guessBase n + s2.mem (wListBase n + j.1)) = s2.mem (digitBase n + j.1) := by
      intro j; simp only [hs2_eq]; exact hg_eq1 j
    have hg_le2 : ∀ v : Fin n, s2.mem (guessBase n + v.1) ≤ 2 :=
      fun v => (hs2_eq _).trans_le (hg_le v)
    set s3 := (Memory.spec 0).clientState s2 (buildTerminalsProg ((n, m), L))
    obtain ⟨hs3_low, hs3_keep, hs3_flip⟩ :=
      buildTerminalsProg_spec (m := m) hG2 hW2 hcol01_2 hg_eq2 hg_le2
    have hG3 : MatrixLoaded G s3 := fun u v =>
      (hs3_low _ (by dsimp only [keepBase]; nlinarith [u.2, v.2])).trans (hG2 u v)
    set sepCnt := (Memory.spec 0).clientResult s3 (minSepProg (n, m))
    set s4 := (Memory.spec 0).clientState s3 (minSepProg (n, m))
    obtain ⟨hs4_low, C, hmin, hcapC_le, hdist_iff, hsepOut, hsepCnt_eq, _⟩ :=
      minSepProg_spec (m := m) hG3
    change ∀ x : Fin (splitCount n), s4.mem (distBase n + x.1) < splitCount n ↔ x ∈ C at hdist_iff
    change ∀ v : Fin n, s4.mem (sepOutBase n + v.1) = _ at hsepOut
    change sepCnt = (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card
      at hsepCnt_eq
    have hs4_s1 : ∀ a < keepBase n, s4.mem a = s1.mem a := fun a ha =>
      (hs4_low a (by dsimp only [keepBase, flowBase] at ha ⊢; omega)).trans
        ((hs3_low a ha).trans (hs2_eq a))
    have hW4 : WListSpec Wset L s4 :=
      hW1.congr fun a _ ha => hs4_s1 a (by dsimp only [digitBase, keepBase] at ha ⊢; omega)
    have hg_eq4 : ∀ j : Fin L,
        s4.mem (guessBase n + s4.mem (wListBase n + j.1)) = s4.mem (digitBase n + j.1) := by
      intro j
      have hL_le := hW.card_le_n
      rw [hs4_s1 (wListBase n + j.1) (by dsimp only [wListBase, keepBase]; omega),
        hs4_s1 (digitBase n + j.1) (by dsimp only [digitBase, keepBase]; omega),
        hs4_s1 (guessBase n + s1.mem (wListBase n + j.1))
          (by dsimp only [guessBase, keepBase]; have := hW1.entry_lt j.1 j.2; omega)]
      exact hg_eq1 j
    have hdelCnt : (Memory.spec 0).clientResult s4 (countDelProg (n, L)) =
        (delSet Wset s4).card := countDelProg_spec hW4 hg_eq4
    set s5 := (Memory.spec 0).clientState s4 (countDelProg (n, L))
    have hs5_eq : ∀ a, s5.mem a = s4.mem a := fun a => preservesAt_countDelProg a _ s4
    have hsepCnt_le : sepCnt ≤ n := by
      rw [hsepCnt_eq]
      exact (Finset.card_le_univ _).trans (by simp)
    have hdel_le : (delSet Wset s4).card ≤ n :=
      (Finset.card_le_univ _).trans (by simp)
    by_cases hsum_le : (delSet Wset s4).card + sepCnt ≤ k
    · have hcond_acc : sepCnt ≤ n ∧ (delSet Wset s4).card ≤ n ∧
          (delSet Wset s4).card + sepCnt ≤ k := ⟨hsepCnt_le, hdel_le, hsum_le⟩
      have hres1 : res = 1 := by
        change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 1
        unfold leafProg
        dsimp only
        rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
          clientResult_bind, clientResult_bind, hdelCnt,
          ite_eq_left hcond_acc, cr_bind_pure]
      have ht_eq : t = (Memory.spec 0).clientState s5 (commitLeafProg n) := by
        change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = _
        unfold leafProg
        dsimp only
        rw [clientState_bind, clientState_bind, hok1, ite_eq_left rfl, clientState_bind,
          clientState_bind, clientState_bind, hdelCnt,
          ite_eq_left hcond_acc, cs_bind_pure]
      refine ⟨by omega, hpres_base, fun h0 => absurd hres1 (by omega), fun _ => ?_⟩
      rw [ht_eq]
      have hW5 : WListSpec Wset L s5 := hW4.congr fun a _ _ => hs5_eq a
      have hcol01_5 : ∀ v : Fin n, s5.mem (colBase n + v.1) ≤ 1 := fun v => by
        rw [hs5_eq, hs4_s1 _ (by dsimp only [colBase, keepBase]; omega)]; exact hcol01_1 v
      obtain ⟨_, hsep_t, hcol01_t, hcW_t, hcW'_t⟩ :=
        commitLeafProg_spec hW5 hcol01_5
      set s6 := (Memory.spec 0).clientState s5 (commitLeafProg n)
      let X : Finset (Fin n) := Finset.univ.filter fun v => s5.mem (sepOutBase n + v.1) = 1
      change ∀ v : Fin n, s6.mem (sepBase n + v.1) =
        if v ∈ delSet Wset s5 ∪ X then 1 else 0 at hsep_t
      have hX_iff : ∀ v : Fin n, v ∈ X ↔ v ∉ Wset ∧ inIdx v ∈ C ∧ outIdx v ∉ C := by
        intro v
        have hv_lt := v.2
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        rw [hs5_eq, hsepOut v,
          hs3_low (wBase n + v.1) (by dsimp only [wBase, keepBase]; omega), hs2_eq,
          hs1_low (wBase n + v.1) (by dsimp only [wBase, guessBase]; omega), hW.w_mem v]
        by_cases hvW : v ∈ Wset <;> by_cases hC : inIdx v ∈ C ∧ outIdx v ∉ C <;> simp [hvW, hC]
      have hdel_eq : delSet Wset s5 = delSet Wset s1 := by
        ext w
        simp only [delSet, Finset.mem_filter, hs5_eq,
          hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
      have hgcol_eq : guessCol n s5 = guessCol n s1 := by
        funext w
        unfold guessCol
        rw [hs5_eq,
          hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
      have hS6 : (Finset.univ.filter fun v : Fin n => s6.mem (sepBase n + v.1) = 1) =
          delSet Wset s5 ∪ X := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsep_t v]
        by_cases h : v ∈ delSet Wset s5 ∪ X <;> simp [h]
      have hX_card : X.card = sepCnt := by
        rw [hsepCnt_eq]
        congr 1
        ext v
        simp [X, hs5_eq]
      have hdel5_card : (delSet Wset s5).card = (delSet Wset s4).card := by
        congr 1; ext w; simp [delSet, hs5_eq]
      refine ⟨fun v => ⟨by rw [hsep_t v]; split_ifs <;> decide, hcol01_t v⟩, ?_⟩
      dsimp only
      rw [hS6]
      refine ⟨(Finset.card_union_le _ _).trans (by omega), ?_⟩
      let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.1) == 1
      let side : Fin n → Bool := fun v => decide (outIdx v ∈ C)
      let c' : Fin n → Bool := fun v => s6.mem (colBase n + v.1) == 1
      have hc₀_s2 : (fun v : Fin n => s2.mem (colBase n + v.1) == 1) = c₀ := by
        funext v
        dsimp only [c₀]
        rw [hs2_eq, hs1_low _ (by dsimp only [colBase, guessBase]; omega)]
      have hdel_s2 : delSet Wset s2 = delSet Wset s1 := by
        ext w; simp [delSet, hs2_eq]
      have hgcol_s2 : guessCol n s2 = guessCol n s1 := by
        funext w; unfold guessCol; rw [hs2_eq]
      have hside_edges : ∀ ⦃u v : Fin n⦄, (prefixGraph G m).Adj u v →
          u ∉ (Wset : Set (Fin n)) → v ∉ (Wset : Set (Fin n)) →
          u ∉ (X : Set (Fin n)) → v ∉ (X : Set (Fin n)) → side u = side v := by
        have hdir : ∀ ⦃u v : Fin n⦄, (prefixGraph G m).Adj u v →
            u ∉ Wset → v ∉ Wset → v ∉ X → outIdx u ∈ C → outIdx v ∈ C := by
          intro u v hadj _ hvW hvX hout_u
          have hcap_uv : (splitNet G m s3).cap (outIdx u) (inIdx v) = n + 1 := by
            unfold splitNet
            dsimp only [outIdx, inIdx]
            have h4 : n + 2 ≤ v.1 + 2 + n ∧ v.1 + 2 + n < splitCount n ∧
                2 ≤ v.1 + 2 ∧ v.1 + 2 < n + 2 := by dsimp only [splitCount]; omega
            have h4' : n + 2 ≤ u.1 + n + 2 ∧ u.1 + n + 2 < splitCount n ∧
                2 ≤ v.1 + 2 ∧ v.1 + 2 < n + 2 := by dsimp only [splitCount]; omega
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              dite_eq_left h4']
            have hu_eq : (⟨u.1 + n + 2 - (n + 2), by dsimp only [splitCount] at h4'; omega⟩ :
                Fin n) = u := Fin.ext (by dsimp only; omega)
            have hv_eq : (⟨v.1 + 2 - 2, by omega⟩ : Fin n) = v := Fin.ext (by dsimp only; omega)
            simp only [hu_eq, hv_eq, hadj, ↓reduceIte]
          have hin_v : inIdx v ∈ C := by
            by_contra hnin
            have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hout_u hnin
            omega
          by_contra hnout
          exact hvX ((hX_iff v).mpr ⟨hvW, hin_v, hnout⟩)
        intro u v hadj huW hvW huX hvX
        dsimp only [side]
        exact decide_eq_decide.mpr ⟨hdir hadj huW hvW hvX, hdir hadj.symm hvW huW huX⟩
      have hkeep_side : ∀ v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
          (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀,
          v ∉ (X : Set (Fin n)) → side v = true := by
        intro v hv hvX
        have hvW : v ∉ Wset := (mem_keepTerminals.mp hv).1
        have hkeep1 : s3.mem (keepBase n + v.1) = 1 := by
          rw [(hs3_keep v).2, hdel_s2, hgcol_s2, hc₀_s2]
          exact hv
        have hcap_0v : (splitNet G m s3).cap (splitNet G m s3).s (inIdx v) = n + 1 := by
          unfold splitNet
          dsimp only [inIdx]
          rw [ite_eq_left rfl, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel,
            ite_eq_left hkeep1]
        have hin_v : inIdx v ∈ C := by
          by_contra hnin
          have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hmin.1.1 hnin
          omega
        have hout_v : outIdx v ∈ C := by
          by_contra hnout
          exact hvX ((hX_iff v).mpr ⟨hvW, hin_v, hnout⟩)
        exact decide_eq_true hout_v
      have hflip_side : ∀ v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
          (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀,
          v ∉ (X : Set (Fin n)) → side v = false := by
        intro v hv _
        have hflip1 : s3.mem (flipBase n + v.1) = 1 := by
          rw [(hs3_flip v).2, hdel_s2, hgcol_s2, hc₀_s2]
          exact hv
        have hcap_v1 : (splitNet G m s3).cap (outIdx v) (splitNet G m s3).t = n + 1 := by
          unfold splitNet
          dsimp only [outIdx]
          rw [ite_eq_right (by omega), ite_eq_left rfl,
            ite_eq_left ⟨by omega, by dsimp only [splitCount]; omega⟩]
          have hsub : v.1 + n + 2 - (n + 2) = v.1 := by omega
          rw [hsub, ite_eq_left hflip1]
        have hout_v : outIdx v ∉ C := fun hout => by
          have hlt := cap_lt_succ_of_cutCapacity_le hcapC_le hout hmin.1.2
          omega
        exact decide_eq_false hout_v
      have hc'_W : ∀ v ∈ (Wset : Set (Fin n)), c' v = guessCol n s1 v := by
        intro v hvW
        rw [← hgcol_eq]
        exact hcW_t v hvW
      have hc'_notW : ∀ v ∉ (Wset : Set (Fin n)), c' v = (c₀ v == side v) := by
        intro v hvW
        have h := hcW'_t v hvW
        dsimp only [c', c₀, side]
        rw [h]
        simp only [hs5_eq]
        rw [hs4_s1 (colBase n + v.1) (by dsimp only [colBase, keepBase]; have := v.2; omega),
          hs1_low (colBase n + v.1) (by dsimp only [colBase, guessBase]; have := v.2; omega)]
        congr 1
        exact decide_eq_decide.mpr (hdist_iff (outIdx v))
      have hproper := proper_of_side (G := prefixGraph G m)
        (W := (Wset : Set (Fin n))) (D := (delSet Wset s1 : Set (Fin n)))
        (X := (X : Set (Fin n))) (c₀ := c₀) (σ := guessCol n s1) (side := side) (c := c')
        (fun u v hadj hu hv => hc₀_prop u v hadj hu hv)
        (fun u v hadj hu hv huD hvD => hprop u hu v hv hadj huD hvD)
        hside_edges hkeep_side hflip_side hc'_W hc'_notW
      intro u v hadj hu hv
      rw [hdel_eq] at hu hv
      exact hproper hadj (by simpa [Finset.coe_union] using hu)
        (by simpa [Finset.coe_union] using hv)
    · have hcond_rej : ¬ (sepCnt ≤ n ∧ (delSet Wset s4).card ≤ n ∧
          (delSet Wset s4).card + sepCnt ≤ k) := fun h => hsum_le h.2.2
      have hres0 : res = 0 := by
        change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 0
        unfold leafProg
        dsimp only
        rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
          clientResult_bind, clientResult_bind, hdelCnt,
          ite_eq_right hcond_rej]
        rfl
      have ht_eq : t = s5 := by
        change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = s5
        unfold leafProg
        dsimp only
        rw [clientState_bind, clientState_bind, hok1, ite_eq_left rfl, clientState_bind,
          clientState_bind, clientState_bind, hdelCnt,
          ite_eq_right hcond_rej]
        rfl
      refine ⟨by omega, hpres_base, fun _ a ha => ?_, fun h1 => absurd hres0 (by omega)⟩
      rw [ht_eq, hs5_eq, hs4_s1 a (by dsimp only [guessBase, keepBase] at ha ⊢; omega),
        hs1_low a ha]
  · have hok0 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 0 := by
      rw [hchk, ite_eq_right hprop]
    have hres0 : res = 0 := by
      change (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 0
      unfold leafProg
      dsimp only
      rw [clientResult_bind, clientResult_bind, hok0, ite_eq_right (by decide : ¬ (0 = 1))]
      rfl
    have ht_eq : t = s2 := by
      change (Memory.spec 0).clientState s (leafProg (((n, k), m), L)) = s2
      unfold leafProg
      dsimp only
      rw [clientState_bind, clientState_bind, hok0, ite_eq_right (by decide : ¬ (0 = 1))]
      rfl
    refine ⟨by omega, hpres_base, fun _ a ha => ?_, fun h1 => absurd hres0 (by omega)⟩
    rw [ht_eq, hs2_eq, hs1_low a ha]

private theorem leafProg_complete_at {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset T : Finset (Fin n)} {cT : Fin n → Bool} {s : Memory.State}
    (hG : MatrixLoaded G s) (hW : WListSpec Wset L s)
    (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1))
    (hTk : T.card ≤ k)
    (hcT : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ T → v ∉ T → cT u ≠ cT v)
    (hdig_T : ∀ j : Fin L, s.mem (digitBase n + j.1) =
      if (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
      else if cT ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ then 2 else 1) :
    (Memory.spec 0).clientResult s (leafProg (((n, k), m), L)) = 1 := by
  have hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2 := by
    intro j hj
    rw [hdig_T ⟨j, hj⟩]
    split_ifs <;> decide
  set s1 := (Memory.spec 0).clientState s (unpackGuessProg (n, L))
  obtain ⟨hs1_low, hg_eq, _, hg_le⟩ := unpackGuessProg_spec hW hdig
  have hG1 : MatrixLoaded G s1 := fun u v =>
    (hs1_low _ (by dsimp only [guessBase]; nlinarith [u.2, v.2])).trans (hG u v)
  have hW1 : WListSpec Wset L s1 :=
    hW.congr fun a _ ha => hs1_low a (by dsimp only [digitBase, guessBase] at ha ⊢; omega)
  have hg_eq1 : ∀ j : Fin L,
      s1.mem (guessBase n + s1.mem (wListBase n + j.1)) = s1.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs1_low (wListBase n + j.1) (by dsimp only [wListBase, guessBase]; omega),
      hs1_low (digitBase n + j.1) (by dsimp only [digitBase, guessBase]; omega)]
    exact hg_eq j
  have hcol01_1 : ∀ v : Fin n, s1.mem (colBase n + v.1) ≤ 1 := fun v =>
    (hs1_low _ (by dsimp only [colBase, guessBase]; omega)).trans_le (hcol01 v)
  have hgw : ∀ w ∈ Wset, s1.mem (guessBase n + w.1) =
      if w ∈ T then 0 else if cT w then 2 else 1 := by
    intro w hwW
    obtain ⟨j, hj⟩ := (hW.mem_iff_exists w).mp hwW
    have hjw : (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) = w := Fin.ext hj
    rw [← hj, hg_eq j, hdig_T j, hjw]
  have hdel_T : delSet Wset s1 = T ∩ Wset := by
    ext w
    simp only [delSet, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hwW, hg0⟩
      rw [hgw w hwW] at hg0
      by_cases hwT : w ∈ T
      · exact ⟨hwT, hwW⟩
      · rw [ite_eq_right hwT] at hg0; split_ifs at hg0
    · rintro ⟨hwT, hwW⟩
      exact ⟨hwW, by rw [hgw w hwW, ite_eq_left hwT]⟩
  have hσ_T : ∀ w ∈ Wset, w ∉ T → guessCol n s1 w = cT w := by
    intro w hwW hwT
    unfold guessCol
    rw [hgw w hwW, ite_eq_right hwT]
    cases cT w <;> rfl
  have hprop : ∀ u ∈ Wset, ∀ v ∈ Wset, (prefixGraph G m).Adj u v →
      u ∉ delSet Wset s1 → v ∉ delSet Wset s1 → guessCol n s1 u ≠ guessCol n s1 v := by
    intro u huW v hvW hadj huD hvD
    have huT : u ∉ T := fun h => huD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, huW⟩)
    have hvT : v ∉ T := fun h => hvD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hvW⟩)
    rw [hσ_T u huW huT, hσ_T v hvW hvT]
    exact hcT u v hadj huT hvT
  have hok1 : (Memory.spec 0).clientResult s1 (checkProperProg ((n, m), L)) = 1 := by
    rw [checkProperProg_spec (m := m) hG1 hW1 hg_eq1 hg_le, ite_eq_left hprop]
  set s2 := (Memory.spec 0).clientState s1 (checkProperProg ((n, m), L))
  have hs2_eq : ∀ a, s2.mem a = s1.mem a := fun a => preservesAt_checkProperProg a _ s1
  have hG2 : MatrixLoaded G s2 := fun u v => (hs2_eq _).trans (hG1 u v)
  have hW2 : WListSpec Wset L s2 := hW1.congr fun a _ _ => hs2_eq a
  have hcol01_2 : ∀ v : Fin n, s2.mem (colBase n + v.1) ≤ 1 :=
    fun v => (hs2_eq _).trans_le (hcol01_1 v)
  have hg_eq2 : ∀ j : Fin L,
      s2.mem (guessBase n + s2.mem (wListBase n + j.1)) = s2.mem (digitBase n + j.1) := by
    intro j; simp only [hs2_eq]; exact hg_eq1 j
  have hg_le2 : ∀ v : Fin n, s2.mem (guessBase n + v.1) ≤ 2 :=
    fun v => (hs2_eq _).trans_le (hg_le v)
  set s3 := (Memory.spec 0).clientState s2 (buildTerminalsProg ((n, m), L))
  obtain ⟨hs3_low, hs3_keep, hs3_flip⟩ :=
    buildTerminalsProg_spec (m := m) hG2 hW2 hcol01_2 hg_eq2 hg_le2
  have hG3 : MatrixLoaded G s3 := fun u v =>
    (hs3_low _ (by dsimp only [keepBase]; nlinarith [u.2, v.2])).trans (hG2 u v)
  set sepCnt := (Memory.spec 0).clientResult s3 (minSepProg (n, m))
  set s4 := (Memory.spec 0).clientState s3 (minSepProg (n, m))
  obtain ⟨hs4_low, C, hmin, _, _, _, hsepCnt_eq, hsepCnt_cap⟩ :=
    minSepProg_spec (m := m) hG3
  change sepCnt = (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card
    at hsepCnt_eq
  change sepCnt ≤ (splitNet G m s3).cutCapacity C at hsepCnt_cap
  have hs4_s1 : ∀ a < keepBase n, s4.mem a = s1.mem a := fun a ha =>
    (hs4_low a (by dsimp only [keepBase, flowBase] at ha ⊢; omega)).trans
      ((hs3_low a ha).trans (hs2_eq a))
  have hW4 : WListSpec Wset L s4 :=
    hW1.congr fun a _ ha => hs4_s1 a (by dsimp only [digitBase, keepBase] at ha ⊢; omega)
  have hg_eq4 : ∀ j : Fin L,
      s4.mem (guessBase n + s4.mem (wListBase n + j.1)) = s4.mem (digitBase n + j.1) := by
    intro j
    have hL_le := hW.card_le_n
    rw [hs4_s1 (wListBase n + j.1) (by dsimp only [wListBase, keepBase]; omega),
      hs4_s1 (digitBase n + j.1) (by dsimp only [digitBase, keepBase]; omega),
      hs4_s1 (guessBase n + s1.mem (wListBase n + j.1))
        (by dsimp only [guessBase, keepBase]; have := hW1.entry_lt j.1 j.2; omega)]
    exact hg_eq1 j
  have hdelCnt : (Memory.spec 0).clientResult s4 (countDelProg (n, L)) =
      (delSet Wset s4).card := countDelProg_spec hW4 hg_eq4
  have hdel4_eq : delSet Wset s4 = T ∩ Wset := by
    rw [← hdel_T]
    ext w
    simp [delSet,
      hs4_s1 (guessBase n + w.1) (by dsimp only [guessBase, keepBase]; have := w.2; omega)]
  let c₀ : Fin n → Bool := fun v => s.mem (colBase n + v.1) == 1
  have hc₀_s2 : (fun v : Fin n => s2.mem (colBase n + v.1) == 1) = c₀ := by
    funext v
    dsimp only [c₀]
    rw [hs2_eq, hs1_low (colBase n + v.1) (by dsimp only [colBase, guessBase]; have := v.2; omega)]
  have hdel_s2 : delSet Wset s2 = delSet Wset s1 := by ext w; simp [delSet, hs2_eq]
  have hgcol_s2 : guessCol n s2 = guessCol n s1 := by funext w; unfold guessCol; rw [hs2_eq]
  let N := splitNet G m s3
  let K : Finset (Fin (splitCount n)) := Finset.univ.filter fun x =>
    x.1 = 0 ∨
      (∃ v : Fin n, x = inIdx v ∧ (v ∈ Wset ∨ v ∈ T ∨ cT v = c₀ v)) ∨
      (∃ v : Fin n, x = outIdx v ∧ v ∉ Wset ∧ v ∉ T ∧ cT v = c₀ v)
  have hK_cut : N.IsCut K := by
    refine ⟨?_, ?_⟩
    · simp [K, N, splitNet]
    · intro h1K
      obtain ⟨_, h1_or⟩ := Finset.mem_filter.mp h1K
      dsimp only [N, splitNet, inIdx, outIdx] at h1_or
      rcases h1_or with h | ⟨v, hv, _⟩ | ⟨v, hv, _⟩
      · omega
      · have := congrArg Fin.val hv; dsimp only at this; omega
      · have := congrArg Fin.val hv; dsimp only at this; omega
  have hK_arcs : ∀ x ∈ K, ∀ y ∈ Finset.univ \ K,
      N.cap x y ≤ if ∃ v ∈ T \ Wset, x = inIdx v ∧ y = outIdx v then 1 else 0 := by
    intro x hx y hy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [K, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases hcap0 : N.cap x y = 0
    · rw [hcap0]; exact Nat.zero_le _
    · unfold N splitNet at hcap0 ⊢
      dsimp only at hcap0 ⊢
      by_cases hx0 : x.1 = 0
      · rw [ite_eq_left hx0] at hcap0 ⊢
        by_cases hy_in : 2 ≤ y.1 ∧ y.1 < n + 2
        · rw [ite_eq_left hy_in] at hcap0
          by_cases hk1 : s3.mem (keepBase n + (y.1 - 2)) = 1
          · exfalso
            let v : Fin n := ⟨y.1 - 2, by omega⟩
            have hy_eq : y = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
            have hkeep_v : v ∈ keepTerminals (prefixGraph G m) (Wset : Set (Fin n))
                (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀ := by
              have hk1' : s3.mem (keepBase n + v.1) = 1 := hk1
              rwa [(hs3_keep v).2, hdel_s2, hgcol_s2, hc₀_s2] at hk1'
            obtain ⟨hvW, w, hwW, hwD, hadj, hne⟩ := mem_keepTerminals.mp hkeep_v
            have hwT : w ∉ T := fun h =>
              hwD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hwW⟩)
            rw [hσ_T w hwW hwT] at hne
            by_cases hvT : v ∈ T
            · exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inl hvT)⟩))
            · have hc_ne := hcT w v hadj hwT hvT
              have hv_eq_c : cT v = c₀ v := by
                revert hne hc_ne
                cases cT w <;> cases cT v <;> cases c₀ v <;> decide
              exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inr hv_eq_c)⟩))
          · rw [ite_eq_right hk1] at hcap0; exact absurd rfl hcap0
        · rw [ite_eq_right hy_in] at hcap0; exact absurd rfl hcap0
      · rw [ite_eq_right hx0] at hcap0 ⊢
        by_cases hy1 : y.1 = 1
        · exfalso
          rw [ite_eq_left hy1] at hcap0
          by_cases hx_out : n + 2 ≤ x.1 ∧ x.1 < splitCount n
          · rw [ite_eq_left hx_out] at hcap0
            let v : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at hx_out; omega⟩
            have hx_eq : x = outIdx v := Fin.ext (by dsimp only [v, outIdx]; omega)
            have hxK : v ∉ Wset ∧ v ∉ T ∧ cT v = c₀ v := by
              rcases hx with h0 | ⟨u, hu, _⟩ | ⟨u, hu, hu_p⟩
              · exact absurd h0 hx0
              · have := congrArg Fin.val hu; dsimp only [inIdx] at this; omega
              · have huv : u = v := Fin.ext (by
                  have := congrArg Fin.val (hx_eq.symm.trans hu)
                  dsimp only [outIdx] at this; omega)
                rwa [← huv]
            by_cases hf1 : s3.mem (flipBase n + v.1) = 1
            · have hflip_v : v ∈ flipTerminals (prefixGraph G m) (Wset : Set (Fin n))
                  (delSet Wset s1 : Set (Fin n)) (guessCol n s1) c₀ := by
                rwa [(hs3_flip v).2, hdel_s2, hgcol_s2, hc₀_s2] at hf1
              obtain ⟨_, w, hwW, hwD, hadj, heq⟩ := mem_flipTerminals.mp hflip_v
              have hwT : w ∉ T := fun h =>
                hwD (by rw [hdel_T]; exact Finset.mem_inter.mpr ⟨h, hwW⟩)
              rw [hσ_T w hwW hwT] at heq
              exact hcT w v hadj hwT hxK.2.1 (heq.trans hxK.2.2.symm)
            · exact hcap0 (ite_eq_right hf1)
          · rw [ite_eq_right hx_out] at hcap0; exact absurd rfl hcap0
        · rw [ite_eq_right hy1] at hcap0 ⊢
          by_cases hx_in : 2 ≤ x.1 ∧ x.1 < n + 2
          · rw [ite_eq_left hx_in] at hcap0 ⊢
            by_cases hy_add : y.1 = x.1 + n
            · rw [ite_eq_left hy_add] at hcap0 ⊢
              let v : Fin n := ⟨x.1 - 2, by omega⟩
              have hx_eq : x = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
              have hy_eq : y = outIdx v := Fin.ext (by dsimp only [v, outIdx]; omega)
              by_cases hw0 : s3.mem (wBase n + v.1) = 0
              · rw [ite_eq_left hw0]
                have hvW : v ∉ Wset := by
                  rw [hs3_low _ (by dsimp only [wBase, keepBase]; omega), hs2_eq,
                    hs1_low _ (by dsimp only [wBase, guessBase]; omega), hW.w_mem v] at hw0
                  by_cases h : v ∈ Wset <;> simp [h] at hw0 ⊢
                have hxK : v ∈ Wset ∨ v ∈ T ∨ cT v = c₀ v := by
                  rcases hx with h0 | ⟨u, hu, hu_p⟩ | ⟨u, hu, _⟩
                  · exact absurd h0 hx0
                  · have huv : u = v := inIdx_injective n (hu.symm.trans hx_eq)
                    rwa [← huv]
                  · have := congrArg Fin.val hu; dsimp only [outIdx] at this; omega
                have hvT : v ∈ T := by
                  rcases hxK with hW' | hT' | hc_eq
                  · exact absurd hW' hvW
                  · exact hT'
                  · by_contra hvT'
                    exact hy (Or.inr (Or.inr ⟨v, hy_eq, hvW, hvT', hc_eq⟩))
                have hex : ∃ u ∈ T \ Wset, x = inIdx u ∧ y = outIdx u :=
                  ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvW⟩, hx_eq, hy_eq⟩
                rw [ite_eq_left hex]
              · exact absurd (ite_eq_right hw0) hcap0
            · rw [ite_eq_right hy_add] at hcap0; exact absurd rfl hcap0
          · exfalso
            rw [ite_eq_right hx_in] at hcap0
            by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2
            · rw [dite_eq_left h4] at hcap0
              let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h4; omega⟩
              let v : Fin n := ⟨y.1 - 2, by omega⟩
              have hx_eq : x = outIdx u := Fin.ext (by dsimp only [u, outIdx]; omega)
              have hy_eq : y = inIdx v := Fin.ext (by dsimp only [v, inIdx]; omega)
              by_cases hadj : (prefixGraph G m).Adj u v
              · have huK : u ∉ Wset ∧ u ∉ T ∧ cT u = c₀ u := by
                  rcases hx with h0 | ⟨z, hz, _⟩ | ⟨z, hz, hz_p⟩
                  · exact absurd h0 hx0
                  · have := congrArg Fin.val hz; dsimp only [inIdx] at this; omega
                  · have hzu : z = u := Fin.ext (by
                      have := congrArg Fin.val (hx_eq.symm.trans hz)
                      dsimp only [outIdx] at this; omega)
                    rwa [← hzu]
                have hvW : v ∉ Wset := fun h => hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inl h⟩))
                have hvT : v ∉ T := fun h => hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inl h)⟩))
                have hc0_ne := hc₀_prop u v hadj huK.1 hvW
                have hcT_ne := hcT u v hadj huK.2.1 hvT
                have hv_eq_c : cT v = c₀ v := by
                  have hcu := huK.2.2
                  change c₀ u ≠ c₀ v at hc0_ne
                  revert hcu hc0_ne hcT_ne
                  cases cT u <;> cases c₀ u <;> cases cT v <;> cases c₀ v <;> decide
                exact hy (Or.inr (Or.inl ⟨v, hy_eq, Or.inr (Or.inr hv_eq_c)⟩))
              · exact hcap0 (ite_eq_right hadj)
            · rw [dite_eq_right h4] at hcap0; exact absurd rfl hcap0
  have hK_row : ∀ x ∈ K,
      (∑ y ∈ Finset.univ \ K, N.cap x y) ≤ if ∃ v ∈ T \ Wset, x = inIdx v then 1 else 0 := by
    intro x hx
    by_cases hex : ∃ v ∈ T \ Wset, x = inIdx v
    · rw [ite_eq_left hex]
      obtain ⟨v, hv, rfl⟩ := hex
      calc ∑ y ∈ Finset.univ \ K, N.cap (inIdx v) y
          ≤ ∑ y ∈ Finset.univ \ K,
              (if ∃ u ∈ T \ Wset, inIdx v = inIdx u ∧ y = outIdx u then 1 else 0) :=
            Finset.sum_le_sum fun y hy => hK_arcs (inIdx v) hx y hy
        _ ≤ ∑ _y ∈ ({outIdx v} : Finset (Fin (splitCount n))), 1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_zero, add_zero,
              Finset.card_singleton]
            refine Finset.card_le_one.mpr fun y₁ hy₁ y₂ hy₂ => ?_
            obtain ⟨_, u₁, _, hu₁, rfl⟩ := Finset.mem_filter.mp hy₁
            obtain ⟨_, u₂, _, hu₂, rfl⟩ := Finset.mem_filter.mp hy₂
            rw [← inIdx_injective n hu₁, ← inIdx_injective n hu₂]
        _ = 1 := by simp
    · rw [ite_eq_right hex]
      refine le_of_eq (Finset.sum_eq_zero fun y hy => ?_)
      have hle := hK_arcs x hx y hy
      have hno : ¬ ∃ v ∈ T \ Wset, x = inIdx v ∧ y = outIdx v :=
        fun ⟨v, hv, hx_eq, _⟩ => hex ⟨v, hv, hx_eq⟩
      rw [ite_eq_right hno] at hle
      omega
  have hK_cap : N.cutCapacity K ≤ (T \ Wset).card := by
    calc N.cutCapacity K
        ≤ ∑ x ∈ K, (if ∃ v ∈ T \ Wset, x = inIdx v then 1 else 0) :=
          Finset.sum_le_sum hK_row
      _ = (K.filter fun x => ∃ v ∈ T \ Wset, x = inIdx v).card := by
          rw [Finset.sum_ite]; simp
      _ ≤ ((T \ Wset).image (inIdx (n := n))).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨_, v, hv, rfl⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      _ = (T \ Wset).card := Finset.card_image_of_injective _ (inIdx_injective n)
  have hsep_le_sdiff : sepCnt ≤ (T \ Wset).card :=
    hsepCnt_cap.trans ((hmin.2 K hK_cut).trans hK_cap)
  have hsum_T : (delSet Wset s4).card + sepCnt ≤ k := by
    rw [hdel4_eq, Finset.inter_comm]
    have hpart := Finset.card_inter_add_card_sdiff T Wset
    have : Wset ∩ T = T ∩ Wset := Finset.inter_comm Wset T
    rw [Finset.inter_comm] at hpart
    omega
  have hsep_le_n : sepCnt ≤ n := by
    rw [hsepCnt_eq]; exact (Finset.card_le_univ _).trans (by simp)
  have hdel_le_n : (delSet Wset s4).card ≤ n := (Finset.card_le_univ _).trans (by simp)
  unfold leafProg
  dsimp only
  rw [clientResult_bind, clientResult_bind, hok1, ite_eq_left rfl, clientResult_bind,
    clientResult_bind, clientResult_bind, hdelCnt,
    ite_eq_left ⟨hsep_le_n, hdel_le_n, hsum_T⟩, cr_bind_pure]

private theorem eq_of_base3At_eq {m₁ m₂ : ℕ → ℕ} {base : ℕ} :
    ∀ {L : ℕ}, (∀ j < L, m₁ (base + j) ≤ 2) → (∀ j < L, m₂ (base + j) ≤ 2) →
      base3At m₁ base L = base3At m₂ base L →
      ∀ j < L, m₁ (base + j) = m₂ (base + j)
  | 0, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | L + 1, h1, h2, heq, j, hj => by
    rw [base3At, base3At] at heq
    have hm1 : min (m₁ (base + L)) 2 = m₁ (base + L) := Nat.min_eq_left (h1 L (by omega))
    have hm2 : min (m₂ (base + L)) 2 = m₂ (base + L) := Nat.min_eq_left (h2 L (by omega))
    rw [hm1, hm2] at heq
    have hlt1 := base3At_lt m₁ base L
    have hlt2 := base3At_lt m₂ base L
    have hd1 := h1 L (by omega)
    have hd2 := h2 L (by omega)
    have hd_eq : m₁ (base + L) = m₂ (base + L) := by
      rcases lt_trichotomy (m₁ (base + L)) (m₂ (base + L)) with hlt | hEq | hgt
      · exfalso
        have hmul : (m₁ (base + L) + 1) * 3 ^ L ≤ m₂ (base + L) * 3 ^ L :=
          Nat.mul_le_mul_right (3 ^ L) hlt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      · exact hEq
      · exfalso
        have hmul : (m₂ (base + L) + 1) * 3 ^ L ≤ m₁ (base + L) * 3 ^ L :=
          Nat.mul_le_mul_right (3 ^ L) hgt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
    have hpre_eq : base3At m₁ base L = base3At m₂ base L := by
      rw [hd_eq] at heq
      exact Nat.add_right_cancel heq
    by_cases hjL : j = L
    · subst hjL; exact hd_eq
    · exact eq_of_base3At_eq (fun i hi => h1 i (by omega)) (fun i hi => h2 i (by omega))
        hpre_eq j (by omega)

private theorem preservesAt_incOdomProg {a : ℕ} {d : ℕ × ℕ}
    (ha : a < digitBase d.1 ∨ digitBase d.1 + d.2 ≤ a) :
    PreservesAt a (incOdomProg d) := by
  unfold incOdomProg
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate_fst 1 fun j hj carry => ⟨?_, fun s => ?_⟩)
    fun _ => preservesAt_pure _ _
  · unfold incOdomStep
    refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
    refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
    refine preservesAt_ite _ ?_ ?_ <;>
      exact preservesAt_bind (preservesAt_write _ (by dsimp only at ha hj ⊢; omega))
        fun _ => preservesAt_pure _ _
  · exact clientResult_incOdomStep_fst _ s

private theorem incOdomProg_digits_le (n L : ℕ) {s : Memory.State}
    (hdig : ∀ j < L, s.mem (digitBase n + j) ≤ 2) :
    ∀ j < L, ((Memory.spec 0).clientState s (incOdomProg (n, L))).mem (digitBase n + j) ≤ 2 := by
  unfold incOdomProg
  rw [clientState_bind_read, cs_bind_pure]
  have hinv := iterate_invariant_of incOdomStep n
    (fun rem (jc : ℕ × ℕ) st =>
      jc.1 + rem = L ∧ ∀ i < L, st.mem (digitBase n + i) ≤ 2)
    (fun rem jc st ⟨hjsum, hle⟩ => by
      unfold incOdomStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hc : jc.2 = 1
      · rw [ite_eq_left hc]
        by_cases hlt : st.mem (digitBase n + jc.1) < 2
        · rw [ite_eq_left hlt, clientResult_bind_write, clientState_bind_write]
          simp only [client_simps]
          refine ⟨by omega, fun i hi => ?_⟩
          by_cases hij : i = jc.1
          · subst hij; rw [Function.update_self]; omega
          · rw [Function.update_of_ne (by omega)]; exact hle i hi
        · rw [ite_eq_right hlt, clientResult_bind_write, clientState_bind_write]
          simp only [client_simps]
          refine ⟨by omega, fun i hi => ?_⟩
          by_cases hij : i = jc.1
          · subst hij; rw [Function.update_self]; decide
          · rw [Function.update_of_ne (by omega)]; exact hle i hi
      · rw [ite_eq_right hc]
        simp only [client_simps]
        exact ⟨by omega, hle⟩)
    (n := L) (a := (0, 1)) (s := s)
    ⟨Nat.zero_add _, hdig⟩
  exact hinv.2

private theorem compressProg_spec {n k m L : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Wset : Finset (Fin n)} {s : Memory.State} (hG : MatrixLoaded G s)
    (hW : WListSpec Wset L s) (hcol01 : ∀ v : Fin n, s.mem (colBase n + v.1) ≤ 1)
    (hc₀_prop : ∀ u v : Fin n, (prefixGraph G m).Adj u v → u ∉ Wset → v ∉ Wset →
      (s.mem (colBase n + u.1) == 1) ≠ (s.mem (colBase n + v.1) == 1)) :
    let res := (Memory.spec 0).clientResult s (compressProg (((n, k), m), L))
    let t := (Memory.spec 0).clientState s (compressProg (((n, k), m), L))
    (∀ a < sepBase n, t.mem a = s.mem a) ∧
      res ≤ 1 ∧
      (res = 1 → OctStateAt G m k t) ∧
      ((∃ T : Finset (Fin n), (prefixGraph G m).IsOddCycleTransversal (T : Set (Fin n)) ∧
        T.card ≤ k) → res = 1) := by
  intro res t
  set s1 := (Memory.spec 0).clientState s (fillRange ((digitBase n, 0), L))
  have hs1 := fillRange_spec (digitBase n) 0 L s
  have hbase3_s1 : base3At s1.mem (digitBase n) L = 0 := by
    have hzero_mem : ∀ k, base3At (fun _ => 0) (digitBase n) k = 0 := fun k => by
      induction k with
      | zero => rfl
      | succ j ih => unfold base3At; rw [ih]; simp
    exact (base3At_congr fun j hj => hs1.1 j hj).trans (hzero_mem L)
  have hs1_pre : ∀ a < digitBase n, s1.mem a = s.mem a := fun a ha => hs1.2 a (Or.inl ha)
  have hleaf_step : ∀ (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      (∀ a < wBase n, u.mem a = s.mem a) →
      let f' := (Memory.spec 0).clientResult u (leafProg (((n, k), m), L))
      let u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
      let u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
      MatrixLoaded G u ∧
        (∀ v : Fin n, u.mem (colBase n + v.1) ≤ 1) ∧
        (∀ x y : Fin n, (prefixGraph G m).Adj x y → x ∉ Wset → y ∉ Wset →
          (u.mem (colBase n + x.1) == 1) ≠ (u.mem (colBase n + y.1) == 1)) ∧
        f' ≤ 1 ∧
        (∀ a < sepBase n, u_odom.mem a = s.mem a) ∧
        WListSpec Wset L u_odom ∧
        (∀ j < L, u_odom.mem (digitBase n + j) ≤ 2) ∧
        (∀ a < digitBase n, u_odom.mem a = u_leaf.mem a) ∧
        base3At u_leaf.mem (digitBase n) L = base3At u.mem (digitBase n) L ∧
        (f' = 0 → ∀ a < digitBase n, u_leaf.mem a = u.mem a) ∧
        (f' = 1 → OctStateAt G m k u_odom) := by
    intro u hlow huW hdig hzero
    have huG : MatrixLoaded G u := fun x y =>
      (hlow _ (by dsimp only [sepBase]; nlinarith [x.2, y.2])).trans (hG x y)
    have hu_col01 : ∀ v : Fin n, u.mem (colBase n + v.1) ≤ 1 := fun v =>
      (hzero _ (by dsimp only [colBase, wBase]; omega)).trans_le (hcol01 v)
    have hu_c0 : ∀ x y : Fin n, (prefixGraph G m).Adj x y → x ∉ Wset → y ∉ Wset →
        (u.mem (colBase n + x.1) == 1) ≠ (u.mem (colBase n + y.1) == 1) := by
      intro x y hadj hx hy
      rw [hzero _ (by dsimp only [colBase, wBase]; omega),
        hzero _ (by dsimp only [colBase, wBase]; omega)]
      exact hc₀_prop x y hadj hx hy
    obtain ⟨hleaf_le, hleaf_pres, hleaf_0, hleaf_1⟩ :=
      leafProg_spec (k := k) huG huW hdig hu_col01 hu_c0
    set u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
    set u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
    have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u_leaf.mem a :=
      fun a ha => preservesAt_incOdomProg (Or.inl ha) u_leaf
    have hL_le := hW.card_le_n
    have hdig_eq : ∀ j < L, u_leaf.mem (digitBase n + j) = u.mem (digitBase n + j) := fun j hj =>
      hleaf_pres _ (Or.inr ⟨by dsimp only [wBase, digitBase]; omega,
        by dsimp only [digitBase, guessBase]; omega⟩)
    have hdig_leaf : ∀ j < L, u_leaf.mem (digitBase n + j) ≤ 2 := fun j hj =>
      (hdig_eq j hj).trans_le (hdig j hj)
    exact ⟨huG, hu_col01, hu_c0, hleaf_le,
      fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
        ((hleaf_pres a (Or.inl ha)).trans (hlow a ha)),
      huW.congr fun a ha1 ha2 => (hodom_pre a ha2).trans
        (hleaf_pres a (Or.inr ⟨ha1, by dsimp only [digitBase, guessBase] at ha2 ⊢; omega⟩)),
      incOdomProg_digits_le n L hdig_leaf,
      hodom_pre,
      base3At_congr hdig_eq,
      fun hf0 a ha => hleaf_0 hf0 a (by dsimp only [digitBase, guessBase] at ha ⊢; omega),
      fun hf1 => (hleaf_1 hf1).congr fun a _ ha2 =>
        hodom_pre a (by dsimp only [wBase, digitBase] at ha2 ⊢; omega)⟩
  have hloop_sound : ∀ rem (st : ℕ × ℕ) (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      st.2 ≤ 1 →
      (st.2 = 0 → ∀ a < wBase n, u.mem a = s.mem a) →
      (st.2 = 1 → OctStateAt G m k u) →
      let r_end := (Memory.spec 0).clientResult u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)
      let u_end := (Memory.spec 0).clientState u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)
      (∀ a < sepBase n, u_end.mem a = s.mem a) ∧
        r_end.2 ≤ 1 ∧
        (r_end.2 = 1 → OctStateAt G m k u_end) := by
    intro rem
    induction rem with
    | zero =>
      intro st u hlow huW _ hst2 _ hoct
      simp only [boundedWhile]
      exact ⟨hlow, hst2, hoct⟩
    | succ rem ih =>
      intro st u hlow huW hdig hst2 hzero_mem hoct
      unfold boundedWhile
      by_cases hg : st.1 = 0
      · simp only [hg, ↓reduceIte]
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
        dsimp only [guessStep]
        rw [clientResult_bind_read, clientState_bind_read]
        by_cases hst2_0 : st.2 = 0
        · rw [ite_eq_left hst2_0, clientResult_bind, clientState_bind, cr_bind_pure, cs_bind_pure]
          obtain ⟨_, _, _, hleaf_le, hlow', huW', hdig', hodom_pre, _, hleaf_0, hoct'⟩ :=
            hleaf_step u hlow huW hdig (hzero_mem hst2_0)
          exact ih _ _ hlow' huW' hdig' hleaf_le
            (fun hf0 a ha => (hodom_pre a (by dsimp only [wBase, digitBase] at ha ⊢; omega)).trans
              ((hleaf_0 hf0 a (by dsimp only [wBase, digitBase] at ha ⊢; omega)).trans
                (hzero_mem hst2_0 a ha)))
            hoct'
        · have hst2_1 : st.2 = 1 := by omega
          rw [ite_eq_right hst2_0, pure_bind, cr_bind_pure, cs_bind_pure]
          set u_odom := (Memory.spec 0).clientState u (incOdomProg (n, L))
          have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u.mem a :=
            fun a ha => preservesAt_incOdomProg (Or.inl ha) u
          exact ih _ u_odom
            (fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
              (hlow a ha))
            (huW.congr fun a _ ha2 => hodom_pre a ha2)
            (incOdomProg_digits_le n L hdig)
            hst2
            (fun h0 => absurd hst2_1 (by omega))
            (fun _ => (hoct hst2_1).congr fun a _ ha2 =>
              hodom_pre a (by dsimp only [wBase, digitBase] at ha2 ⊢; omega))
      · simp only [hg, ↓reduceIte]
        exact ⟨hlow, hst2, hoct⟩
  have hs1_W : WListSpec Wset L s1 := hW.congr fun a _ ha => hs1_pre a ha
  have hs1_dig : ∀ j < L, s1.mem (digitBase n + j) ≤ 2 := fun j hj => by
    rw [hs1.1 j hj]; decide
  obtain ⟨hlow_fin, hres_le, hres_sound⟩ := hloop_sound (3 ^ L) (0, 0) s1
    (fun a ha => hs1_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega))
    hs1_W hs1_dig (by decide)
    (fun _ a ha => hs1_pre a (by dsimp only [wBase, digitBase] at ha ⊢; omega))
    (fun h => absurd h (by decide))
  have ht_eq : t = (Memory.spec 0).clientState s1
      (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) (3 ^ L) (0, 0)) := by
    change (Memory.spec 0).clientState s (compressProg (((n, k), m), L)) = _
    unfold compressProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, cs_bind_pure]
  have hres_eq : res = ((Memory.spec 0).clientResult s1
      (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L)
        (3 ^ L) (0, 0))).2 := by
    change (Memory.spec 0).clientResult s (compressProg (((n, k), m), L)) = _
    unfold compressProg
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, cr_bind_pure]
  rw [ht_eq, hres_eq]
  refine ⟨hlow_fin, hres_le, hres_sound, ?_⟩
  rintro ⟨T, hToct, hTk⟩
  obtain ⟨cT, hcT⟩ := isOddCycleTransversal_iff_exists_bool.mp hToct
  let dgTarget : ℕ → ℕ := fun a =>
    if h : digitBase n ≤ a ∧ a - digitBase n < L then
      let w : Fin n := ⟨s.mem (wListBase n + (a - digitBase n)), hW.entry_lt _ h.2⟩
      if w ∈ T then 0 else if cT w then 2 else 1
    else 0
  have hdgTarget_at : ∀ j : Fin L, dgTarget (digitBase n + j.1) =
      if (⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
      else if cT ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ then 2 else 1 := by
    intro j
    dsimp only [dgTarget]
    have hcond : digitBase n ≤ digitBase n + j.1 ∧ digitBase n + j.1 - digitBase n < L :=
      ⟨by omega, by have := j.2; omega⟩
    rw [dite_eq_left hcond]
    have hsub : digitBase n + j.1 - digitBase n = j.1 := Nat.add_sub_cancel_left _ _
    have hw_eq : (⟨s.mem (wListBase n + (digitBase n + j.1 - digitBase n)),
        hW.entry_lt _ hcond.2⟩ : Fin n) =
        ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ :=
      Fin.ext (by dsimp only; rw [hsub])
    rw [hw_eq]
  have hdgTarget_le : ∀ j < L, dgTarget (digitBase n + j) ≤ 2 := by
    intro j hj
    rw [hdgTarget_at ⟨j, hj⟩]
    split_ifs <;> decide
  let targetVal := base3At dgTarget (digitBase n) L
  have htarget_lt : targetVal < 3 ^ L := base3At_lt dgTarget (digitBase n) L
  have hloop_comp : ∀ rem (st : ℕ × ℕ) (u : Memory.State),
      (∀ a < sepBase n, u.mem a = s.mem a) →
      WListSpec Wset L u →
      (∀ j < L, u.mem (digitBase n + j) ≤ 2) →
      st.2 ≤ 1 →
      (st.2 = 0 → ∀ a < digitBase n, u.mem a = s.mem a) →
      (st.1 = 0 → 3 ^ L ≤ base3At u.mem (digitBase n) L + rem) →
      (st.2 = 1 ∨ (st.1 = 0 ∧ base3At u.mem (digitBase n) L ≤ targetVal)) →
      ((Memory.spec 0).clientResult u
        (boundedWhile (fun _ (x : ℕ × ℕ) => x.1 = 0) guessStep (((n, k), m), L) rem st)).2 = 1 := by
    intro rem
    induction rem with
    | zero =>
      intro st u _ _ _ _ _ hbudget hor
      rcases hor with hfound1 | ⟨hg0, _⟩
      · unfold boundedWhile; simp only [client_simps]; exact hfound1
      · have hlt := base3At_lt u.mem (digitBase n) L
        have := hbudget hg0
        omega
    | succ rem ih =>
      intro st u hlow huW hdig hst2 hzero_mem hbudget hor
      unfold boundedWhile
      by_cases hg : st.1 = 0
      · simp only [hg, ↓reduceIte]
        rw [StateTransitionSpec.clientResult_bind]
        dsimp only [guessStep]
        rw [clientResult_bind_read, clientState_bind_read]
        by_cases hst2_0 : st.2 = 0
        · rw [ite_eq_left hst2_0, clientResult_bind, clientState_bind, cr_bind_pure, cs_bind_pure]
          obtain ⟨huG, hu_col01, hu_c0, hleaf_le, hlow', huW', hdig', hodom_pre, hbase_leaf,
              hleaf_0, _⟩ :=
            hleaf_step u hlow huW hdig
              (fun a ha => hzero_mem hst2_0 a (by dsimp only [wBase, digitBase] at ha ⊢; omega))
          set u_leaf := (Memory.spec 0).clientState u (leafProg (((n, k), m), L))
          set f' := (Memory.spec 0).clientResult u (leafProg (((n, k), m), L))
          set done' := (Memory.spec 0).clientResult u_leaf (incOdomProg (n, L))
          set u_odom := (Memory.spec 0).clientState u_leaf (incOdomProg (n, L))
          have hodom := incOdomProg_base3At n L u_leaf
          change done' ≤ 1 ∧ base3At u_odom.mem (digitBase n) L + done' * 3 ^ L =
              base3At u_leaf.mem (digitBase n) L + 1 at hodom
          obtain ⟨hdone_le, hodom_eq⟩ := hodom
          rw [hbase_leaf] at hodom_eq
          have hbud := hbudget hg
          have hle_tar : base3At u.mem (digitBase n) L ≤ targetVal :=
            (hor.resolve_left (by omega)).2
          refine ih (done', f') u_odom hlow' huW' hdig' hleaf_le
            (fun hf0 a ha => (hodom_pre a ha).trans
              ((hleaf_0 hf0 a ha).trans (hzero_mem hst2_0 a ha)))
            (fun hd0 => by dsimp only at hd0; rw [hd0, zero_mul, add_zero] at hodom_eq; omega)
            ?_
          dsimp only
          by_cases hf1 : f' = 1
          · exact Or.inl hf1
          · have hf0 : f' = 0 := by omega
            by_cases heq_tar : base3At u.mem (digitBase n) L = targetVal
            · exfalso
              have hdig_eq := eq_of_base3At_eq hdig hdgTarget_le heq_tar
              have hdig_u : ∀ j : Fin L, u.mem (digitBase n + j.1) =
                  if (⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ : Fin n) ∈ T then 0
                  else if cT ⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ then 2 else 1 := by
                intro j
                have hL_le := hW.card_le_n
                have hwl_u : u.mem (wListBase n + j.1) = s.mem (wListBase n + j.1) :=
                  hzero_mem hst2_0 _ (by dsimp only [wListBase, digitBase]; omega)
                have hfin_eq : (⟨u.mem (wListBase n + j.1), huW.entry_lt j.1 j.2⟩ : Fin n) =
                    ⟨s.mem (wListBase n + j.1), hW.entry_lt j.1 j.2⟩ := Fin.ext hwl_u
                rw [hdig_eq j.1 j.2, hdgTarget_at j, hfin_eq]
              have hf1' : f' = 1 :=
                leafProg_complete_at (k := k) huG huW hu_col01 hu_c0 hTk hcT hdig_u
              omega
            · have hlt_tar : base3At u.mem (digitBase n) L < targetVal := by omega
              have hd0 : done' = 0 := by
                by_contra hne0
                have hd1 : done' = 1 := by omega
                rw [hd1, one_mul] at hodom_eq
                dsimp only [targetVal] at hlt_tar htarget_lt
                omega
              refine Or.inr ⟨hd0, ?_⟩
              rw [hd0, zero_mul, add_zero] at hodom_eq
              dsimp only [targetVal] at hlt_tar ⊢
              omega
        · have hst2_1 : st.2 = 1 := by omega
          rw [ite_eq_right hst2_0, pure_bind, cr_bind_pure, cs_bind_pure]
          set done' := (Memory.spec 0).clientResult u (incOdomProg (n, L))
          set u_odom := (Memory.spec 0).clientState u (incOdomProg (n, L))
          have hodom_pre : ∀ a < digitBase n, u_odom.mem a = u.mem a :=
            fun a ha => preservesAt_incOdomProg (Or.inl ha) u
          have hodom := incOdomProg_base3At n L u
          change done' ≤ 1 ∧ base3At u_odom.mem (digitBase n) L + done' * 3 ^ L =
              base3At u.mem (digitBase n) L + 1 at hodom
          obtain ⟨_, hodom_eq⟩ := hodom
          have hbud := hbudget hg
          exact ih (done', st.2) u_odom
            (fun a ha => (hodom_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega)).trans
              (hlow a ha))
            (huW.congr fun a _ ha2 => hodom_pre a ha2)
            (incOdomProg_digits_le n L hdig)
            hst2
            (fun h0 => absurd hst2_1 (by omega))
            (fun hd0 => by dsimp only at hd0; rw [hd0, zero_mul, add_zero] at hodom_eq; omega)
            (Or.inl hst2_1)
      · rcases hor with hfound1 | ⟨hg0, _⟩
        · simp only [hg, ↓reduceIte, client_simps]; exact hfound1
        · exact absurd hg0 hg
  exact hloop_comp (3 ^ L) (0, 0) s1
    (fun a ha => hs1_pre a (by dsimp only [sepBase, digitBase] at ha ⊢; omega))
    hs1_W hs1_dig (by decide)
    (fun _ a ha => hs1_pre a ha)
    (fun _ => by rw [hbase3_s1, zero_add])
    (Or.inr ⟨rfl, by rw [hbase3_s1]; exact Nat.zero_le _⟩)

/-! ### Outer vertex-addition loop and uniform Word-RAM program -/

private theorem memoryCost_buildWProg_le (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (buildWProg d) s ≤ 5 * (d.1 + 1) := by
  rcases d with ⟨n, m⟩
  dsimp only
  unfold buildWProg
  dsimp only
  have hstep : ∀ vL t, memoryCost (buildWListStep (n, vL)) t ≤ 2 := fun vL t => by
    unfold buildWListStep
    exact le_trans (memoryCost_bind_le (mc_read _ t) fun _ t' =>
      memoryCost_ite_le ((le_refl 1)) (Nat.zero_le _)) (by decide)
  have hcopy := memoryCost_copyRange_le ((sepBase n, wBase n), n) s
  exact le_trans (memoryCost_bind_le hcopy fun _ t1 =>
    memoryCost_bind_le (mc_write _ _ t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of buildWListStep 2 n hstep n (0, 0) t2)
        fun _ t3 => mc_pure _ t3) (by dsimp only; omega)

private theorem iterate_inv_and_cost {δ σ : Type} (body : δ × σ → Memory.Prog σ)
    (c : ℕ) (d : δ) (Inv : ℕ → σ → Memory.State → Prop)
    (hstep : ∀ rem a t, Inv (rem + 1) a t →
      memoryCost (body (d, a)) t ≤ c ∧
        Inv rem ((Memory.spec 0).clientResult t (body (d, a)))
          ((Memory.spec 0).clientState t (body (d, a)))) :
    ∀ m a s, Inv m a s →
      memoryCost (iterate body d m a) s ≤ c * m ∧
        Inv 0 ((Memory.spec 0).clientResult s (iterate body d m a))
          ((Memory.spec 0).clientState s (iterate body d m a))
  | 0, a, s, h => ⟨by simp [iterate], h⟩
  | m + 1, a, s, h => by
    obtain ⟨hc1, hinv1⟩ := hstep m a s h
    obtain ⟨hcm, hinvm⟩ := iterate_inv_and_cost body c d Inv hstep m _ _ hinv1
    dsimp only [iterate]
    refine ⟨?_, ?_⟩
    · rw [memoryCost_bind', Nat.mul_succ]
      omega
    · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      exact hinvm

private theorem octProg_cost_arith (n k : ℕ) :
    1 + (1 + ((octScratch n + 1) + (n + (n + 655 * 3 ^ k * (n + 1) ^ 4 * n)))) ≤
      680 * 3 ^ k * (n + 1) ^ 5 := by
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hscr_le : octScratch n + 1 ≤ 22 * (n + 1) ^ 5 := by
    unfold octScratch splitCount
    nlinarith [Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 2 ≤ 5)]
  have hn_le : n ≤ (n + 1) ^ 5 := by
    have : n + 1 ≤ (n + 1) ^ 5 := by
      simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 5)
    omega
  have hmul_n : 655 * 3 ^ k * (n + 1) ^ 4 * n ≤ 655 * 3 ^ k * (n + 1) ^ 5 := by
    calc 655 * 3 ^ k * (n + 1) ^ 4 * n
        ≤ 655 * 3 ^ k * (n + 1) ^ 4 * (n + 1) := Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ = 655 * 3 ^ k * (n + 1) ^ 5 := by ring
  have hp5_pos : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow 5 (n + 1) (Nat.succ_pos n)
  nlinarith

private theorem octProg_spec_and_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) :
    let s₀ := Memory.State.init (encodeInput G k)
    let res := (Memory.spec 0).clientResult s₀ (octProg ())
    let t := (Memory.spec 0).clientState s₀ (octProg ())
    memoryCost (octProg ()) s₀ ≤ 680 * 3 ^ k * (n + 1) ^ 5 ∧
      res ≤ 1 ∧
      (res = 1 ↔ ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k) ∧
      (res = 1 → OctStateAt G n k t) := by
  intro s₀ res t
  have hs₀_1 : s₀.mem 1 = n := by
    change (if (1 : ℕ) = 0 then (encodeInput G k).length
      else (encodeInput G k).getD (1 - 1) 0) = n
    rfl
  have hs₀_2 : s₀.mem 2 = k := by
    change (if (2 : ℕ) = 0 then (encodeInput G k).length
      else (encodeInput G k).getD (2 - 1) 0) = k
    rfl
  have hs₀_fr : s₀.frontier = 3 + n * n := by
    simp only [s₀, Memory.State.init, length_encodeInput]
    omega
  have hG₀ : MatrixLoaded G s₀ := matrixLoaded_init G k
  set s_al := (Memory.spec 0).clientState s₀ (Memory.alloc (octScratch n))
  have hs_al_pre : ∀ a < 3 + n * n, s_al.mem a = s₀.mem a := fun a ha => by
    have ha_fr : a < s₀.frontier := by rw [hs₀_fr]; exact ha
    exact Memory.mem_step_of_lt_frontier s₀ (.alloc (octScratch n)) ha_fr (by simp)
  set s_sep := (Memory.spec 0).clientState s_al (fillRange ((sepBase n, 0), n))
  have hs_sep := fillRange_spec (sepBase n) 0 n s_al
  set s_col := (Memory.spec 0).clientState s_sep (fillRange ((colBase n, 0), n))
  have hs_col := fillRange_spec (colBase n) 0 n s_sep
  have hs_col_G : MatrixLoaded G s_col := fun u v => by
    have ha1 : 3 + u.1 * n + v.1 < colBase n := by dsimp only [colBase]; nlinarith [u.2, v.2]
    have ha2 : 3 + u.1 * n + v.1 < sepBase n := by dsimp only [sepBase]; nlinarith [u.2, v.2]
    rw [hs_col.2 _ (Or.inl ha1), hs_sep.2 _ (Or.inl ha2), hs_al_pre _ ha2]
    exact hG₀ u v
  have hoct0 : OctStateAt G 0 k s_col := by
    have hsep0 : ∀ v : Fin n, s_col.mem (sepBase n + v.1) = 0 := fun v =>
      (hs_col.2 _ (Or.inl (by dsimp only [sepBase, colBase]; omega))).trans (hs_sep.1 v.1 v.2)
    have hcol0 : ∀ v : Fin n, s_col.mem (colBase n + v.1) = 0 := fun v => hs_col.1 v.1 v.2
    refine ⟨fun v => ⟨by rw [hsep0]; decide, by rw [hcol0]; decide⟩, ?_⟩
    dsimp only
    have hempty : (Finset.univ.filter fun v : Fin n => s_col.mem (sepBase n + v.1) = 1) = ∅ := by
      ext v; simp [hsep0 v]
    rw [hempty]
    exact ⟨Nat.zero_le k, fun u _ hadj => absurd hadj.2.1 (Nat.not_lt_zero _)⟩
  have hp1_4 : n + 1 ≤ (n + 1) ^ 4 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 4)
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  let LoopInv (rem : ℕ) (ma : ℕ × ℕ) (st : Memory.State) : Prop :=
    ma.1 + rem = n ∧
    MatrixLoaded G st ∧
    ma.2 ≤ 1 ∧
    (ma.2 = 1 → OctStateAt G ma.1 k st) ∧
    (ma.2 = 0 → ¬ ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k)
  have hstep : ∀ rem (ma : ℕ × ℕ) st, LoopInv (rem + 1) ma st →
      memoryCost (octStep ((n, k), ma)) st ≤ 655 * 3 ^ k * (n + 1) ^ 4 ∧
        LoopInv rem ((Memory.spec 0).clientResult st (octStep ((n, k), ma)))
          ((Memory.spec 0).clientState st (octStep ((n, k), ma))) := by
    intro rem ⟨m, alive⟩ st ⟨hmsum, hG_st, hal_le, hal1, hal0⟩
    have hm_lt : m < n := by omega
    by_cases hal : alive = 1
    · obtain ⟨h01_st, hS_card, hS_prop⟩ := hal1 hal
      set S : Finset (Fin n) := Finset.univ.filter fun v => st.mem (sepBase n + v.1) = 1
      let Wset : Finset (Fin n) := insert ⟨m, hm_lt⟩ S
      obtain ⟨htW_low, hW⟩ := buildWProg_spec hm_lt fun v => (h01_st v).1
      set L := (Memory.spec 0).clientResult st (buildWProg (n, m))
      set tW := (Memory.spec 0).clientState st (buildWProg (n, m))
      have hL_le_n : L ≤ n := hW.card_le_n
      have hL_le_k1 : L ≤ k + 1 := by
        rw [hW.card_eq]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hS_card 1)
      have hcW_prop : ∀ u v : Fin n, (prefixGraph G (m + 1)).Adj u v →
          u ∉ Wset → v ∉ Wset →
          (tW.mem (colBase n + u.1) == 1) ≠ (tW.mem (colBase n + v.1) == 1) := by
        intro u v ⟨hadj, hum1, hvm1⟩ huW hvW
        have hum : u.1 ≠ m :=
          fun h => huW ((Fin.ext h : u = ⟨m, hm_lt⟩) ▸ Finset.mem_insert_self _ _)
        have hvm : v.1 ≠ m :=
          fun h => hvW ((Fin.ext h : v = ⟨m, hm_lt⟩) ▸ Finset.mem_insert_self _ _)
        have huS : u ∉ S := fun h => huW (Finset.mem_insert_of_mem h)
        have hvS : v ∉ S := fun h => hvW (Finset.mem_insert_of_mem h)
        rw [htW_low _ (by dsimp only [colBase, wBase]; omega),
          htW_low _ (by dsimp only [colBase, wBase]; omega)]
        exact hS_prop u v ⟨hadj, by omega, by omega⟩ huS hvS
      have hG_tW : MatrixLoaded G tW := fun u v =>
        (htW_low _ (by dsimp only [wBase]; nlinarith [u.2, v.2])).trans (hG_st u v)
      have hcost_step : memoryCost (octStep ((n, k), (m, alive))) st ≤
          655 * 3 ^ k * (n + 1) ^ 4 := by
        unfold octStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read]
        change 1 + memoryCost (if alive = 1 then _ else _) st ≤ _
        rw [ite_eq_left hal, memoryCost_bind']
        have hbw := memoryCost_buildWProg_le (n, m) st
        dsimp only at hbw
        by_cases hLk : L ≤ k
        · rw [ite_eq_left hLk]
          have hw_mc : memoryCost (do Memory.write (sepBase n + m) 1; pure (m + 1, 1)) tW ≤ 1 :=
            (le_refl 1)
          nlinarith [hp1_4, hpow3]
        · rw [ite_eq_right hLk, ite_eq_left hL_le_n]
          have hcp := memoryCost_compressProg_le (d := (((n, k), m + 1), L)) hL_le_n tW
          dsimp only at hcp
          have hcp_map : memoryCost
              (do let ok ← compressProg (((n, k), m + 1), L); pure (m + 1, ok)) tW ≤
              215 * 3 ^ L * (n + 1) ^ 4 :=
            le_trans (memoryCost_bind_le hcp fun _ t' => mc_pure _ t') (by omega)
          have hL_eq : L = k + 1 := by omega
          have hpowL : 3 ^ L = 3 * 3 ^ k := by rw [hL_eq, pow_succ, Nat.mul_comm]
          rw [hpowL] at hcp_map
          nlinarith [hp1_4, hpow3]
      refine ⟨hcost_step, ?_⟩
      unfold octStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, ite_eq_left hal, clientResult_bind,
        clientState_bind]
      change LoopInv rem ((Memory.spec 0).clientResult tW (if L ≤ k then _ else _))
        ((Memory.spec 0).clientState tW (if L ≤ k then _ else _))
      by_cases hLk : L ≤ k
      · rw [ite_eq_left hLk, clientResult_bind_write, clientState_bind_write, clientResult_pure,
        clientState_pure]
        dsimp only [LoopInv]
        refine ⟨by omega, fun u v => ?_, by decide, fun _ => ?_, fun h0 => absurd h0 (by decide)⟩
        · dsimp only
          rw [Function.update_of_ne (by dsimp only [sepBase]; nlinarith [u.2, v.2])]
          exact hG_tW u v
        · refine ⟨fun v => ⟨?_, ?_⟩, ?_⟩
          · dsimp only
            by_cases hvm : v.1 = m
            · rw [hvm, Function.update_self]
            · rw [Function.update_of_ne (by omega),
                htW_low _ (by dsimp only [sepBase, wBase]; omega)]
              exact (h01_st v).1
          · dsimp only
            rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              htW_low _ (by dsimp only [colBase, wBase]; omega)]
            exact (h01_st v).2
          · dsimp only
            have hS_new : (Finset.univ.filter fun v : Fin n =>
                Function.update tW.mem (sepBase n + m) 1 (sepBase n + v.1) = 1) = Wset := by
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Wset, Finset.mem_insert, S]
              by_cases hvm : v.1 = m
              · have hveq : v = ⟨m, hm_lt⟩ := Fin.ext hvm
                subst hveq
                dsimp only
                rw [Function.update_self]
                simp
              · have hne : v ≠ ⟨m, hm_lt⟩ := fun h => hvm (congrArg Fin.val h)
                rw [Function.update_of_ne (by omega),
                  htW_low _ (by dsimp only [sepBase, wBase]; omega)]
                simp [hne]
            rw [hS_new, ← hW.card_eq]
            refine ⟨hLk, fun u v hadj huW hvW => ?_⟩
            rw [Function.update_of_ne (by dsimp only [sepBase, colBase]; omega),
              Function.update_of_ne (by dsimp only [sepBase, colBase]; omega)]
            exact hcW_prop u v hadj huW hvW
      · rw [ite_eq_right hLk, ite_eq_left hL_le_n, cr_bind_pure, cs_bind_pure]
        have hcol01_tW : ∀ v : Fin n, tW.mem (colBase n + v.1) ≤ 1 := fun v =>
          (htW_low _ (by dsimp only [colBase, wBase]; omega)).trans_le (h01_st v).2
        obtain ⟨hcp_low, hcp_le, hcp_sound, hcp_comp⟩ :=
          compressProg_spec (k := k) (m := m + 1) hG_tW hW hcol01_tW hcW_prop
        set ok := (Memory.spec 0).clientResult tW (compressProg (((n, k), m + 1), L))
        set tC := (Memory.spec 0).clientState tW (compressProg (((n, k), m + 1), L))
        dsimp only [LoopInv]
        refine ⟨by omega,
          fun u v => (hcp_low _ (by dsimp only [sepBase]; nlinarith [u.2, v.2])).trans (hG_tW u v),
          hcp_le, hcp_sound, fun hok0 ⟨T, hToct, hTk⟩ => ?_⟩
        have h1 : ok = 1 := hcp_comp ⟨T, hToct.anti (prefixGraph_le G (m + 1)), hTk⟩
        omega
    · have hal_eq0 : alive = 0 := by omega
      have hcost_dead : memoryCost (octStep ((n, k), (m, alive))) st ≤
          655 * 3 ^ k * (n + 1) ^ 4 := by
        unfold octStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read]
        change 1 + memoryCost (if alive = 1 then _ else _) st ≤ _
        rw [ite_eq_right hal]
        have : memoryCost (pure (m + 1, 0) : Memory.Prog (ℕ × ℕ)) st = 0 := rfl
        rw [this]
        nlinarith [hp1_4, hpow3]
      refine ⟨hcost_dead, ?_⟩
      unfold octStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, ite_eq_right hal]
      simp only [client_simps]
      dsimp only [LoopInv]
      exact ⟨by omega, hG_st, by decide, fun h => absurd h (by decide), fun _ => hal0 hal_eq0⟩
  obtain ⟨hiter_cost, hinv_end⟩ := iterate_inv_and_cost octStep (655 * 3 ^ k * (n + 1) ^ 4)
    (n, k) LoopInv hstep n (0, 1) s_col
    ⟨Nat.zero_add _, hs_col_G, by decide, fun _ => hoct0, fun h => absurd h (by decide)⟩
  set ma_end := (Memory.spec 0).clientResult s_col (iterate octStep (n, k) n (0, 1))
  set s_end := (Memory.spec 0).clientState s_col (iterate octStep (n, k) n (0, 1))
  obtain ⟨hm_end, _, hal_end_le, hal_end_1, hal_end_0⟩ := hinv_end
  have hm_eq_n : ma_end.1 = n := by omega
  rw [hm_eq_n] at hal_end_1
  have hres_eq : res = ma_end.2 := by
    change (Memory.spec 0).clientResult s₀ (octProg ()) = ma_end.2
    unfold octProg
    rw [clientResult_bind_read, clientResult_bind_read, hs₀_1, hs₀_2, clientResult_bind,
      clientResult_bind,
      clientResult_bind, cr_bind_pure]
  have ht_eq : t = s_end := by
    change (Memory.spec 0).clientState s₀ (octProg ()) = s_end
    unfold octProg
    rw [clientState_bind_read, clientState_bind_read, hs₀_1, hs₀_2, clientState_bind,
      clientState_bind,
      clientState_bind, cs_bind_pure]
  have htotal_cost : memoryCost (octProg ()) s₀ ≤ 680 * 3 ^ k * (n + 1) ^ 5 := by
    unfold octProg
    have hr1 : (Memory.spec 0).clientResult s₀ (Memory.read 1) = n := hs₀_1
    have hcs1 : (Memory.spec 0).clientState s₀ (Memory.read 1) = s₀ := rfl
    have hr2 : (Memory.spec 0).clientResult s₀ (Memory.read 2) = k := hs₀_2
    have hcs2 : (Memory.spec 0).clientState s₀ (Memory.read 2) = s₀ := rfl
    rw [memoryCost_bind', memoryCost_read, hr1, hcs1, memoryCost_bind', memoryCost_read, hr2, hcs2,
      memoryCost_bind', memoryCost_alloc]
    change 1 + (1 + ((octScratch n + 1) +
        memoryCost (do
          fillRange ((sepBase n, 0), n)
          fillRange ((colBase n, 0), n)
          let res ← iterate octStep (n, k) n (0, 1)
          pure res.2) s_al)) ≤ 680 * 3 ^ k * (n + 1) ^ 5
    rw [memoryCost_bind']
    change 1 + (1 + ((octScratch n + 1) +
        (memoryCost (fillRange ((sepBase n, 0), n)) s_al +
          memoryCost (do
            fillRange ((colBase n, 0), n)
            let res ← iterate octStep (n, k) n (0, 1)
            pure res.2) s_sep))) ≤ 680 * 3 ^ k * (n + 1) ^ 5
    rw [memoryCost_bind']
    change 1 + (1 + ((octScratch n + 1) +
        (memoryCost (fillRange ((sepBase n, 0), n)) s_al +
          (memoryCost (fillRange ((colBase n, 0), n)) s_sep +
            memoryCost (do let res ← iterate octStep (n, k) n (0, 1); pure res.2) s_col)))) ≤
      680 * 3 ^ k * (n + 1) ^ 5
    have hc_sep := memoryCost_fillRange_le ((sepBase n, 0), n) s_al
    have hc_col := memoryCost_fillRange_le ((colBase n, 0), n) s_sep
    dsimp only at hc_sep hc_col
    have hc_pure : memoryCost (do let res ← iterate octStep (n, k) n (0, 1); pure res.2) s_col ≤
        655 * 3 ^ k * (n + 1) ^ 4 * n :=
      le_trans (memoryCost_bind_le hiter_cost fun _ u => mc_pure _ u) (by omega)
    exact le_trans (by omega) (octProg_cost_arith n k)
  rw [hres_eq, ht_eq]
  refine ⟨htotal_cost, hal_end_le, ⟨fun h1 => ?_, fun hex => ?_⟩, hal_end_1⟩
  · obtain ⟨_, hcard, hprop⟩ := hal_end_1 h1
    let S := Finset.univ.filter fun v : Fin n => s_end.mem (sepBase n + v.1) = 1
    refine ⟨S, isOddCycleTransversal_iff_exists_bool.mpr ⟨fun v => s_end.mem (colBase n + v.1) == 1,
      fun u v hadj hu hv => ?_⟩, hcard⟩
    rw [← prefixGraph_of_le G (le_refl n)] at hadj
    exact hprop u v hadj hu hv
  · by_cases h1 : ma_end.2 = 1
    · exact h1
    · exact absurd hex (hal_end_0 (by omega))

/-- **Word-RAM odd cycle transversal by iterative compression**: a single uniform flat program over
`Basis.exact` decides whether an `n`-vertex simple graph `G` has an odd cycle transversal of size at
most `k` within `C * 3 ^ k * (n + 1) ^ 5` instructions whenever `Fits w (octWorkspace n)` and
`Fits w k`, agreeing with `Cslib.Algorithms.Lean.IterativeCompression.oct` and materializing a
valid transversal at `sepAddr n` and a proper Boolean colouring off it at `colAddr n` on
yes-instances. -/
theorem exists_oct_program :
    ∃ r C pc : ℕ, 0 < C ∧ ∃ prog : Program .exact r,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k w : ℕ),
        Fits w (octWorkspace n) → Fits w k →
        ∃ (y : Data r) (steps res : ℕ),
          Runs w prog (State.init (encodeInput G k)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * 3 ^ k * (n + 1) ^ 5 ∧
          res ≤ 1 ∧
          (res = 1 ↔ (oct G k).isSome) ∧
          (res = 1 ↔
            ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k) ∧
          (res = 1 →
            (∀ v : Fin n, y.mem (sepAddr n v.1) ≤ 1 ∧ y.mem (colAddr n v.1) ≤ 1) ∧
            let S : Finset (Fin n) := Finset.univ.filter fun v => y.mem (sepAddr n v.1) = 1
            G.IsOddCycleTransversal (S : Set (Fin n)) ∧ S.card ≤ k ∧
              ∀ u v : Fin n, G.Adj u v → u ∉ S → v ∉ S →
                (y.mem (colAddr n u.1) == 1) ≠ (y.mem (colAddr n v.1) == 1)) := by
  obtain ⟨r, C₀, pc, prog, frontier, _, hprog⟩ :=
    octProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨r, 681 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n G _ k w hw hk
  let words := encodeInput G k
  have hlen_fit : Fits w (words.length + 1) := by
    rw [length_encodeInput]
    exact hw.of_le (by dsimp only [octWorkspace]; omega)
  have hin_fit : InputFits w words := by
    refine ⟨by rw [length_encodeInput]; exact hw.of_le (by dsimp only [octWorkspace]; omega), ?_⟩
    intro v hv
    simp only [words, encodeInput, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv_mat
    · exact hw.of_le (by dsimp only [octWorkspace]; omega)
    · exact hk
    · simp only [encodeAdjMatrix, List.mem_ofFn] at hv_mat
      obtain ⟨idx, rfl⟩ := hv_mat
      split_ifs
      · exact hw.of_le (by dsimp only [octWorkspace]; omega)
      · exact fits_zero w
  have hs₀_1 : (Memory.State.init words).mem 1 = n := rfl
  have hsafe : (Memory.State.init words).frontier =
      3 + (Memory.State.init words).mem 1 * (Memory.State.init words).mem 1 ∧
      Fits w (octWorkspace ((Memory.State.init words).mem 1)) := by
    rw [hs₀_1]
    exact ⟨by simp [Memory.State.init, words, length_encodeInput]; omega, hw⟩
  have hv := validHistory_octProg (G := G) hw hk
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () words (fun j => Fin.elim0 j) (Nat.zero_le _) hlen_fit hin_fit hsafe hv
  rw [clientResult_width w (octProg ())] at hhalt
  rw [clientState_width w (octProg ())] at hmem
  obtain ⟨hmc, hres_le, hres_iff, hres_oct⟩ := octProg_spec_and_cost G k
  set res := (Memory.spec 0).clientResult (Memory.State.init words) (octProg ())
  have hout_eq : WordEncoding.encode (α := ℕ) res 0 = res := rfl
  rw [hout_eq] at hhalt
  have hymem : y.mem = ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem :=
    congrArg Memory.State.mem hmem
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hp5 : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow 5 (n + 1) (Nat.succ_pos n)
  have h1_le : 1 ≤ 3 ^ k * (n + 1) ^ 5 := Nat.mul_le_mul hpow3 hp5
  have hsteps_le : steps + 1 ≤ (681 * C₀ + 2) * 3 ^ k * (n + 1) ^ 5 := by
    dsimp only [words] at hbound
    calc steps + 1
        ≤ C₀ * (memoryCost (octProg ()) (Memory.State.init (encodeInput G k)) + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (680 * 3 ^ k * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left C₀ (by omega)) 1
      _ ≤ C₀ * (681 * 3 ^ k * (n + 1) ^ 5) + 2 * (3 ^ k * (n + 1) ^ 5) := by nlinarith
      _ = (681 * C₀ + 2) * 3 ^ k * (n + 1) ^ 5 := by ring
  refine ⟨y, steps, res, hruns, hhalt, hsteps_le, hres_le,
    hres_iff.trans oct_isSome_iff.symm, hres_iff, fun h1 => ?_⟩
  obtain ⟨h01, hcard, hprop⟩ := hres_oct h1
  have hsep_addr : ∀ v : Fin n, y.mem (sepAddr n v.1) =
      ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
        (sepBase n + v.1) := fun v => by rw [hymem]; rfl
  have hcol_addr : ∀ v : Fin n, y.mem (colAddr n v.1) =
      ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
        (colBase n + v.1) := fun v => by rw [hymem]; rfl
  refine ⟨fun v => ⟨(hsep_addr v).trans_le (h01 v).1, (hcol_addr v).trans_le (h01 v).2⟩, ?_⟩
  dsimp only
  have hS_eq : (Finset.univ.filter fun v : Fin n => y.mem (sepAddr n v.1) = 1) =
      (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) := by
    ext v; simp [hsep_addr v]
  rw [hS_eq]
  have hpropG : ∀ u v : Fin n, G.Adj u v →
      u ∉ (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) →
      v ∉ (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) →
      (y.mem (colAddr n u.1) == 1) ≠ (y.mem (colAddr n v.1) == 1) := by
    intro u v hadj hu hv
    rw [hcol_addr u, hcol_addr v]
    rw [← prefixGraph_of_le G (le_refl n)] at hadj
    exact hprop u v hadj hu hv
  exact ⟨isOddCycleTransversal_iff_exists_bool.mpr
      ⟨fun v => y.mem (colAddr n v.1) == 1, fun u v hadj hu hv => hpropG u v hadj hu hv⟩,
    hcard, hpropG⟩

/-! ### Packaged decision problem and `UniformDecidableInTime` certificates -/

/-- Packaged instance of the parameterized odd-cycle-transversal decision problem: a simple graph
`G` on `Fin n` with decidable adjacency together with parameter `k`. -/
structure OctInstance where
  /-- Number of vertices. -/
  n : ℕ
  /-- Solution-size bound. -/
  k : ℕ
  /-- Input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidable adjacency relation on `G`. -/
  [decAdj : DecidableRel G.Adj]

attribute [instance] OctInstance.decAdj

/-- Word-RAM encoding of an `OctInstance` as `encodeInput x.G x.k`. -/
@[expose] def OctInstance.encode (x : OctInstance) : List ℕ :=
  encodeInput x.G x.k

/-- The yes-instances of `OctInstance`: graphs admitting an odd cycle transversal of size `≤ k`. -/
@[expose] def OctInstance.Yes : Set OctInstance :=
  {x | ∃ T : Finset (Fin x.n), x.G.IsOddCycleTransversal (T : Set (Fin x.n)) ∧ T.card ≤ x.k}

/-- **Uniform FPT Word-RAM decision for odd cycle transversal** at every word width fitting
`octWorkspace x.n`. -/
theorem uniformDecidableInTime_oct :
    ∃ C : ℕ, 0 < C ∧
      UniformDecidableInTime .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5)
        (fun x w => Fits w (octWorkspace x.n)) := by
  obtain ⟨r, C, pc, hC_pos, prog, hprog⟩ := exists_oct_program
  refine ⟨C, hC_pos, r, prog, ?_, ?_⟩
  · intro x w hw hin
    have hk : Fits w x.k :=
      hin.2 x.k (by simp [OctInstance.encode, encodeInput])
    obtain ⟨y, steps, res, hruns, hhalt, htime, hres_le, _, hres_iff, _⟩ :=
      hprog x.G x.k w hw hk
    exact ⟨res, steps + 1, ⟨⟨pc, y⟩, steps, hruns, hhalt, rfl⟩, htime, hres_le, hres_iff⟩
  · intro x
    obtain ⟨w, hlow, hin⟩ :=
      InputFits.exists_width x.encode (Nat.log 2 (octWorkspace x.n) + 1)
    have hw_fit : Fits w (octWorkspace x.n) := by
      have hlt : octWorkspace x.n < 2 ^ (Nat.log 2 (octWorkspace x.n) + 1) :=
        Nat.lt_pow_succ_log_self Nat.one_lt_two _
      exact Fits.mono hlt hlow
    exact ⟨w, hw_fit, hin⟩

/-- **Uniform FPT Word-RAM decision for odd cycle transversal** under the transdichotomous
logarithmic word-size convention (`size x = x.encode.length`). -/
theorem uniformDecidableInTimeLogWord_oct :
    ∃ C : ℕ, 0 < C ∧
      UniformDecidableInTimeLogWord .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x => x.encode.length)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5) := by
  obtain ⟨C, hC_pos, hdec⟩ := uniformDecidableInTime_oct
  refine ⟨C, hC_pos, 4, by decide, hdec.mono (fun _ _ => le_rfl) ?_
    (inputAdmissible_of_widthIndependent OctInstance.encode _)⟩
  intro x w hw
  have hlt : octWorkspace x.n < (x.encode.length + 1) ^ 4 := by
    simp only [OctInstance.encode, length_encodeInput, octWorkspace]
    let M := x.n * x.n + 3
    have hM : 3 ≤ M := Nat.le_add_left 3 (x.n * x.n)
    have hM2 : 9 ≤ M * M := by nlinarith
    have h3M : 3 * M ≤ M * M := by nlinarith
    have hn_le : x.n ≤ x.n * x.n + 1 := by nlinarith
    calc 5 * (x.n * x.n) + 21 * x.n + 11
        < 9 * (3 * M) := by dsimp only [M]; nlinarith
      _ ≤ (M * M) * (M * M) := Nat.mul_le_mul hM2 h3M
      _ = (2 + x.n * x.n + 1) ^ 4 := by dsimp only [M]; ring
  exact (fits_of_lt_pow hlt).mono hw

end Cslib.Algorithms.WordRAM.OddCycleTransversal
